import Fe.Sonatina.Syntax

/-!
# Decidable equality of the IR

The checkers compare instructions, terminators and whole functions; their soundness needs the
comparison to be equality, which the derived `BEq` of `Syntax.lean` does not state.
-/

namespace Fe.Sonatina

deriving instance DecidableEq for Ty
deriving instance DecidableEq for Operand
deriving instance DecidableEq for BinOp
deriving instance DecidableEq for CmpOp
deriving instance DecidableEq for OvfOp
deriving instance DecidableEq for CastOp
deriving instance DecidableEq for EvmOp
deriving instance DecidableEq for Inst
deriving instance DecidableEq for Term
deriving instance DecidableEq for Phi
deriving instance DecidableEq for Stmt
deriving instance DecidableEq for Block
deriving instance DecidableEq for Func
deriving instance DecidableEq for Module

end Fe.Sonatina
