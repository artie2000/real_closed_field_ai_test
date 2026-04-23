import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

open Polynomial

namespace IsRealClosed

universe u
variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

private lemma not_isSquare_neg_one : ¬ IsSquare (-1 : R) := by
  intro hsq
  have h : (0 : R) ≤ -1 := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := -1)).mpr hsq
  linarith

private lemma irreducible_X_sq_add_one :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  have h : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1) := by simp [map_neg, map_one, sub_neg_eq_add]
  have hmonic : (X ^ 2 - C (-1 : R)).Monic := monic_X_pow_sub_C _ (by decide)
  have hdeg : (X ^ 2 - C (-1 : R)).natDegree = 2 := natDegree_X_pow_sub_C
  rw [h]
  rw [Polynomial.Monic.irreducible_iff_roots_eq_zero_of_degree_le_three hmonic
        (by rw [hdeg]) (by rw [hdeg]; decide),
      Multiset.eq_zero_iff_forall_notMem]
  intro c hc
  rw [mem_roots hmonic.ne_zero] at hc
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_neg_eq_add] at hc
  have hsq : IsSquare (-1 : R) := ⟨c, by linear_combination hc.symm - sq c⟩
  exact not_isSquare_neg_one hsq

private abbrev Ri (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] : Type u := AdjoinRoot (X ^ 2 + 1 : R[X])

private instance : Fact (Irreducible (X ^ 2 + 1 : R[X])) := ⟨irreducible_X_sq_add_one⟩

private noncomputable instance : Module.Finite R (Ri R) :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis irreducible_X_sq_add_one.ne_zero).basis

theorem Ri_isSquare (z : Ri R) : IsSquare z := by
  have hirred : Irreducible (X ^ 2 + 1 : R[X]) := irreducible_X_sq_add_one
  have hmonic : (X ^ 2 + 1 : R[X]).Monic := by
    have h : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1 : R) := by simp [sub_neg_eq_add]
    rw [h]; exact monic_X_pow_sub_C _ (by decide)
  have hdeg2 : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
    have h : (X ^ 2 + 1 : R[X]) = X ^ 2 - C (-1 : R) := by simp [sub_neg_eq_add]
    rw [h]; exact natDegree_X_pow_sub_C
  set hm : IsAdjoinRootMonic (Ri R) (X ^ 2 + 1 : R[X]) :=
    AdjoinRoot.isAdjoinRootMonic (X ^ 2 + 1 : R[X]) hmonic
  have hroot_sq : hm.root ^ 2 = -1 := by
    have heq : hm.root = AdjoinRoot.root (X ^ 2 + 1 : R[X]) := rfl
    have h0 : aeval (AdjoinRoot.root (X ^ 2 + 1 : R[X])) (X ^ 2 + 1 : R[X]) = 0 :=
      AdjoinRoot.eval₂_root _
    simp [aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_one,
          add_eq_zero_iff_eq_neg] at h0
    rw [heq]; exact h0
  -- decomposition via power basis
  have hrepr : ∀ x : Ri R,
      x = algebraMap R (Ri R) (hm.coeff x 0) +
          algebraMap R (Ri R) (hm.coeff x 1) * hm.root := by
    intro x
    apply hm.ext_elem
    intro i hi
    rw [hdeg2] at hi
    have hroot_coeff : hm.coeff hm.root = Pi.single 1 1 :=
      hm.coeff_root (by rw [hdeg2]; decide)
    have hcoeff_aM_mul_root : ∀ (c : R) (j : ℕ),
        hm.coeff (algebraMap R (Ri R) c * hm.root) j =
          c • (Pi.single (M := fun _ : ℕ => R) 1 1) j := by
      intro c j
      rw [show algebraMap R (Ri R) c * hm.root = c • hm.root from by rw [Algebra.smul_def],
          LinearMap.map_smul hm.coeff]
      show c • hm.coeff hm.root j = _
      rw [hroot_coeff]
    interval_cases i
    · rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
      show hm.coeff x 0 = (Pi.single 0 (hm.coeff x 0) : ℕ → R) 0
          + hm.coeff (algebraMap R (Ri R) (hm.coeff x 1) * hm.root) 0
      rw [hcoeff_aM_mul_root]; simp
    · rw [LinearMap.map_add hm.coeff, hm.coeff_algebraMap]
      show hm.coeff x 1 = (Pi.single 0 (hm.coeff x 0) : ℕ → R) 1
          + hm.coeff (algebraMap R (Ri R) (hm.coeff x 1) * hm.root) 1
      rw [hcoeff_aM_mul_root]; simp
  -- name the coefficients
  set a : R := hm.coeff z 0
  set b : R := hm.coeff z 1
  have hz : z = algebraMap R (Ri R) a + algebraMap R (Ri R) b * hm.root := hrepr z
  -- r = √(a^2 + b^2) exists
  have hnn : (0 : R) ≤ a ^ 2 + b ^ 2 := by positivity
  obtain ⟨r, hr⟩ :=
    (IsRealClosed.nonneg_iff_isSquare (R := R) (x := a ^ 2 + b ^ 2)).mp hnn
  -- r * r = a^2 + b^2; pick nonneg root
  -- Use |r| to get a nonneg square root
  set r' : R := |r|
  have hr'_nn : 0 ≤ r' := abs_nonneg r
  have hr'_sq : r' * r' = a ^ 2 + b ^ 2 := by
    rw [show r' * r' = r * r from by rcases abs_choice r with h | h <;>
      rw [show r' = _ from h] <;> ring]
    exact hr.symm
  -- r' ≥ a since r'^2 ≥ a^2
  have hr'_ge_abs_a : |a| ≤ r' := by
    have : a ^ 2 ≤ r' ^ 2 := by
      rw [show r' ^ 2 = r' * r' from sq r', hr'_sq]
      nlinarith [sq_nonneg b]
    have habs_a : 0 ≤ |a| := abs_nonneg a
    nlinarith [sq_abs a, sq_nonneg (|a| - r'), sq_nonneg (|a| + r')]
  have hr'_ge_a : a ≤ r' := le_trans (le_abs_self a) hr'_ge_abs_a
  have hr'_ge_neg_a : -a ≤ r' := le_trans (neg_le_abs a) hr'_ge_abs_a
  -- Case analysis
  by_cases hb0 : b = 0
  · -- b = 0, z = a (in R)
    rw [hb0] at hz
    simp only [map_zero, zero_mul, add_zero] at hz
    by_cases ha_nn : 0 ≤ a
    · -- z = a, IsSquare a in R, pull back through algebraMap
      obtain ⟨s, hs⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := a)).mp ha_nn
      refine ⟨algebraMap R (Ri R) s, ?_⟩
      rw [hz, hs]; simp [map_mul]
    · -- a < 0, so -a > 0, has square root s; then (s * i)^2 = -a * -1 = a
      push_neg at ha_nn
      have hna_nn : 0 ≤ -a := by linarith
      obtain ⟨s, hs⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R) (x := -a)).mp hna_nn
      refine ⟨algebraMap R (Ri R) s * hm.root, ?_⟩
      have step1 :
          (algebraMap R (Ri R) s * hm.root) * (algebraMap R (Ri R) s * hm.root)
          = (algebraMap R (Ri R) s * algebraMap R (Ri R) s) * (hm.root * hm.root) := by
        ring
      have hmul : algebraMap R (Ri R) s * algebraMap R (Ri R) s
                    = algebraMap R (Ri R) (-a) := by
        rw [← map_mul, ← hs]
      have hii : hm.root * hm.root = -1 := by rw [← sq]; exact hroot_sq
      rw [step1, hmul, hii, hz]
      rw [show algebraMap R (Ri R) (-a) * (-1 : Ri R) = algebraMap R (Ri R) a from by
        rw [map_neg]; ring]
  · -- b ≠ 0, so r' > 0 and a + r' > 0
    have hb2_pos : 0 < b ^ 2 := by positivity
    have hr'2_pos : 0 < r' ^ 2 := by
      rw [show r' ^ 2 = r' * r' from sq r', hr'_sq]; nlinarith [sq_nonneg a]
    have hr'_pos : 0 < r' := by
      rcases lt_or_eq_of_le hr'_nn with h | h
      · exact h
      · exfalso; rw [← h] at hr'2_pos; norm_num at hr'2_pos
    -- a + r' > 0
    have hapr_pos : 0 < a + r' := by
      -- If a + r' = 0, then a = -r'. Then a^2 = r'^2 = a^2 + b^2, so b = 0, contradiction.
      by_contra h
      push_neg at h
      have happ_le : a + r' ≤ 0 := h
      have : -a = r' := by linarith [hr'_ge_neg_a, happ_le]
      have ha_sq : a ^ 2 = r' ^ 2 := by nlinarith
      have : b ^ 2 = 0 := by
        have := hr'_sq
        have hr'sq : r' ^ 2 = a ^ 2 + b ^ 2 := by rw [sq]; exact this
        linarith
      have : b = 0 := pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp this
      exact hb0 this
    -- u = √((a + r')/2), v = b/(2u)
    have hu_nn : 0 ≤ (a + r') / 2 := by linarith
    obtain ⟨u, hu⟩ :=
      (IsRealClosed.nonneg_iff_isSquare (R := R) (x := (a + r') / 2)).mp hu_nn
    set u' : R := |u|
    have hu'_nn : 0 ≤ u' := abs_nonneg u
    have hu'_sq : u' * u' = (a + r') / 2 := by
      rw [show u' * u' = u * u from by rcases abs_choice u with h | h <;>
        rw [show u' = _ from h] <;> ring]
      exact hu.symm
    have hu'_pos : 0 < u' := by
      rcases lt_or_eq_of_le hu'_nn with h | h
      · exact h
      · exfalso; rw [← h] at hu'_sq; linarith
    have hu'_ne : u' ≠ 0 := ne_of_gt hu'_pos
    let v : R := b / (2 * u')
    -- verify u'^2 - v^2 = a and 2*u'*v = b
    have h2u'_ne : (2 * u' : R) ≠ 0 := by positivity
    have hv_rel : 2 * u' * v = b := by
      show 2 * u' * (b / (2 * u')) = b
      field_simp
    have hu'2 : u' ^ 2 = (a + r') / 2 := by rw [sq]; exact hu'_sq
    have hv2 : v ^ 2 = b ^ 2 / (4 * u' ^ 2) := by
      show (b / (2 * u')) ^ 2 = b ^ 2 / (4 * u' ^ 2)
      field_simp; ring
    have hu'2_sub_v2 : u' ^ 2 - v ^ 2 = a := by
      rw [hu'2, hv2, hu'2]
      have hfour_pos : (0 : R) < 4 * ((a + r') / 2) := by linarith
      have hfour_ne : (4 * ((a + r') / 2) : R) ≠ 0 := ne_of_gt hfour_pos
      have hr'_sq' : r' ^ 2 = a ^ 2 + b ^ 2 := by rw [sq]; exact hr'_sq
      field_simp
      nlinarith [hr'_sq']
    -- Now witness: u' + v*i
    refine ⟨algebraMap R (Ri R) u' + algebraMap R (Ri R) v * hm.root, ?_⟩
    rw [hz]
    set i : Ri R := hm.root
    set A : Ri R := algebraMap R (Ri R) u'
    set B : Ri R := algebraMap R (Ri R) v
    have hi2 : i * i = -1 := by
      show hm.root * hm.root = -1
      rw [← sq]; exact hroot_sq
    have hsq :
        (A + B * i) * (A + B * i)
        = (A * A - B * B) + (A * B + A * B) * i := by
      have : B * i * (B * i) = -(B * B) := by
        calc B * i * (B * i) = (B * B) * (i * i) := by ring
          _ = (B * B) * (-1) := by rw [hi2]
          _ = -(B * B) := by ring
      calc (A + B * i) * (A + B * i)
          = A * A + A * (B * i) + B * i * A + B * i * (B * i) := by ring
        _ = A * A + A * B * i + A * B * i + (-(B * B)) := by rw [this]; ring
        _ = (A * A - B * B) + (A * B + A * B) * i := by ring
    rw [hsq]
    have hAA : A * A = algebraMap R (Ri R) (u' * u') := by
      show algebraMap R (Ri R) u' * algebraMap R (Ri R) u' = _
      rw [← map_mul]
    have hBB : B * B = algebraMap R (Ri R) (v * v) := by
      show algebraMap R (Ri R) v * algebraMap R (Ri R) v = _
      rw [← map_mul]
    have hAB : A * B + A * B = algebraMap R (Ri R) (2 * u' * v) := by
      show algebraMap R (Ri R) u' * algebraMap R (Ri R) v
          + algebraMap R (Ri R) u' * algebraMap R (Ri R) v = _
      rw [← map_mul, ← map_add]
      congr 1; ring
    rw [hAA, hBB, hAB, ← map_sub]
    have heq_a : u' * u' - v * v = a := by
      have h1 : u' * u' = u' ^ 2 := by rw [sq]
      have h2 : v * v = v ^ 2 := by rw [sq]
      rw [h1, h2]; exact hu'2_sub_v2
    rw [heq_a, hv_rel]

end IsRealClosed
