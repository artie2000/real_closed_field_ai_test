/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib
import RealClosedField.Algebra.Order.Field.RealClosed

namespace IsRealClosed

variable (R : Type*) [Field R] [IsRealClosed R]

/-- FTA for real closed fields: any finite extension of R has dimension at most 2. -/
theorem finrank_le_two_of_finiteDimensional'
    (K : Type*) [Field K] [Algebra R K] [FiniteDimensional R K] :
    Module.finrank R K ≤ 2 := by
  sorry

end IsRealClosed
