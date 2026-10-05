import Bapat.Certificate

/-! # The exact coefficient-list shape, including the cancelled leading term -/

namespace Bapat.Certificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem coefficient_shape :
    coefficients.1.length = 145 ∧ coefficients.2.length = 144 ∧
      coefficients.2.drop 143 = [zero] := by
  decide +kernel

#print axioms coefficient_shape

end Bapat.Certificate
