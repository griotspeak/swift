//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2016 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See http://swift.org/LICENSE.txt for license information
// See http://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//
//
//  This file implements implicit derivation of the DiscriminatedUnion protocol.
//
//===----------------------------------------------------------------------===//

#include "TypeChecker.h"
#include "swift/AST/Decl.h"
#include "swift/AST/Stmt.h"
#include "swift/AST/Expr.h"
#include "swift/AST/Types.h"
#include "llvm/Support/raw_ostream.h"
#include "DerivedConformances.h"

using namespace swift;

/// Common preconditions for DiscriminatedUnion.
static bool canDeriveConformance(NominalTypeDecl *type) {
  // The type must be an enum.
  auto enumDecl = dyn_cast<EnumDecl>(type);
  if (!enumDecl)
    return false;

  // "Simple" enums without availability attributes can derive
  // a DiscriminatedUnion conformance.
  //
  // FIXME: Lift the availability restriction.
  return !enumDecl->hasPotentiallyUnavailableCaseValue(); // FIXME: Other conditions?
}

/// Derive the implementation of discriminant for a "simple" no-payload enum.
static std::pair<BraceStmt *, bool>
deriveDiscriminatedUnion_enum_getter(AbstractFunctionDecl *funcDecl, void *) {
  // Copy from rawValue derived conformance
  auto *parentDC = funcDecl->getDeclContext();
  auto *parentEnum = parentDC->getSelfEnumDecl();
  auto enumTy = parentDC->getDeclaredTypeInContext();
  auto &C = parentDC->getASTContext();

  SmallVector<Expr *, 8> elExprs;
  for (EnumElementDecl *elt : parentEnum->getAllElements()) {
    auto *ref = new (C) DeclRefExpr(elt, DeclNameLoc(), /*implicit*/true);
    auto *base = TypeExpr::createImplicit(enumTy, C);
    auto *apply = new (C) DotSyntaxCallExpr(ref, SourceLoc(), base);
    elExprs.push_back(apply);
  }
  auto *arrayExpr = ArrayExpr::create(C, SourceLoc(), elExprs, {}, SourceLoc());

  auto *returnStmt = new (C) ReturnStmt(SourceLoc(), arrayExpr);
  auto *body = BraceStmt::create(C, SourceLoc(), ASTNode(returnStmt),
                                 SourceLoc());
  return { body, /*isTypeChecked=*/false };
}

static Type computeDiscriminantType(NominalTypeDecl *enumDecl) {
  auto enumType = enumDecl->getDeclaredInterfaceType();
  if (!enumType || enumType->hasError())
    return nullptr;

  return enumType;
}

/// Synthesizes a new \c CodingKeys enum based on the {En,De}codable members of
/// the given type (\c nullptr if unable to synthesize).
///
/// If able to synthesize the enum, adds it directly to \c derived.Nominal.
static EnumDecl *synthesizeDiscriminantEnum(DerivedConformance &derived) {
  auto &tc = derived.TC;
  auto &C = tc.Context;
  // Create CodingKeys in the parent type always, because both
  // Encodable and Decodable might want to use it, and they may have
  // different conditional bounds. CodingKeys is simple and can't
  // depend on those bounds.
  auto target = derived.Nominal;

  // We want to look through all the var declarations of this type to create
  // enum cases based on those var names.
  auto *discriminatedUnionProto = C.getProtocol(KnownProtocolKind::Hashable);
  auto *discriminatedUnionType = discriminatedUnionProto->getDeclaredType();
  TypeLoc protoTypeLoc[1] = {TypeLoc::withoutLoc(discriminatedUnionType)};
  MutableArrayRef<TypeLoc> inherited = C.AllocateCopy(protoTypeLoc);

  auto *enumDecl = new (C) EnumDecl(SourceLoc(), C.Id_Discriminant, SourceLoc(),
                                    inherited, nullptr, target);
  enumDecl->setImplicit();
  enumDecl->setAccess(AccessLevel::Public);

  // // Each of these vars needs a case in the enum. For each var decl, if the type
  // // conforms to {En,De}codable, add it to the enum.
  // bool allConform = true;
  // for (auto *varDecl : target->getStoredProperties()) {
  //   if (!varDecl->isUserAccessible())
  //     continue;
  //
  //   // Despite creating the enum in the context of the type, we're
  //   // concurrently checking the variables for the current protocol
  //   // conformance being synthesized, for which we use the conformance
  //   // context, not the type.
  //   auto conformance = varConformsToCodable(tc, derived.getConformanceContext(),
  //                                           varDecl, derived.Protocol);
  //   switch (conformance) {
  //     case Conforms:
  //     {
  //       auto *elt = new (C) EnumElementDecl(SourceLoc(),
  //                                           getVarNameForCoding(varDecl),
  //                                           nullptr, SourceLoc(), nullptr,
  //                                           enumDecl);
  //       elt->setImplicit();
  //       enumDecl->addMember(elt);
  //       break;
  //     }
  //
  //     case DoesNotConform:
  //       tc.diagnose(varDecl->getLoc(),
  //                   diag::codable_non_conforming_property_here,
  //                   derived.getProtocolType(), varDecl->getType());
  //       LLVM_FALLTHROUGH;
  //
  //     case TypeNotValidated:
  //       // We don't produce a diagnostic for a type which failed to validate.
  //       // This will produce a diagnostic elsewhere anyway.
  //       allConform = false;
  //       continue;
  //   }
  // }
  //
  // if (!allConform)
  //   return nullptr;

  // Forcibly derive conformance to CodingKey.
  tc.checkConformancesInContext(enumDecl, enumDecl);

  // Add to the type.
  target->addMember(enumDecl);
  return enumDecl;
}

static Type deriveDiscriminatedUnion_Discriminant(DerivedConformance &derived) {
  // enum SomeEnum : DiscriminatedUnion {
  //   @derived
  //   enum Discriminant {}
  // }
  auto *discriminantEnum = synthesizeDiscriminantEnum(derived);
    
  auto rawInterfaceType = computeDiscriminantType(discriminantEnum);
  return derived.getConformanceContext()->mapTypeIntoContext(rawInterfaceType);
}

ValueDecl *DerivedConformance::deriveDiscriminatedUnion(ValueDecl *requirement) {
  // Conformance can't be synthesized in an extension.
  if (checkAndDiagnoseDisallowedContext(requirement))
    return nullptr;

  // Check that we can actually derive DiscriminatedUnion for this type.
  if (!canDeriveConformance(Nominal))
    return nullptr;

  ASTContext &C = TC.Context;

  // Build the necessary decl.
  if (requirement->getBaseName() != C.Id_discriminant) {
    requirement->diagnose(diag::broken_case_iterable_requirement); // FIXME: Update
    return nullptr;
  }


  // Define the property.
  auto returnTy = computeDiscriminantType(Nominal);

  VarDecl *propDecl;
  PatternBindingDecl *pbDecl;
  std::tie(propDecl, pbDecl) =
      declareDerivedProperty(C.Id_discriminant, returnTy, returnTy,
                             /*isStatic=*/false, /*isFinal=*/true);

  // Define the getter.
  auto *getterDecl = addGetterToReadOnlyDerivedProperty(propDecl, returnTy);

  getterDecl->setBodySynthesizer(&deriveDiscriminatedUnion_enum_getter);

  addMembersToConformanceContext({propDecl, pbDecl});

  return propDecl;
}

Type DerivedConformance::deriveDiscriminatedUnion(AssociatedTypeDecl *assocType) {
  llvm::errs() << "Place 1\n";
  if (checkAndDiagnoseDisallowedContext(assocType)) 
    return nullptr;

  llvm::errs() << "Place 2\n";
  // Check that we can actually derive DiscriminatedUnion for this type.
  if (!canDeriveConformance(Nominal))
    return nullptr;
  
  llvm::errs() << "Place 3\n";

  if (assocType->getName() == TC.Context.Id_Discriminant) {
    llvm::errs() << "Place 4\n";
    auto back = deriveDiscriminatedUnion_Discriminant(*this);
    back.dump();
    return back;
  }
  
  llvm::errs() << "Place 5\n";

  TC.diagnose(assocType->getLoc(), diag::broken_case_iterable_requirement);
  return nullptr;
}

