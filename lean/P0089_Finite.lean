import Mathlib

/-!
# Finite steps of "The local limit of sublinear preferential attachment graphs with fixed out-degree"

Three pieces of the paper that are finite algebra:

* Lemma `Degrees` (sec_apriori.tex): with `L_i = Σ_{s=i}^{n-1} 1/s`, `Σ_{i ≤ n} L_i = n - 1` and
  `Σ_{i ≤ n} L_i^2 = Σ_{s,t<n} min(s,t)/(st) = 2(n-1) - H_{n-1} ≤ 2(n-1)`.
  Here `N = n - 1` and indices are shifted down by one: `L N i = Σ_{s ∈ [i, N)} 1/(s+1)`.
* The normalisation step of Lemma `forcedS` (sec_local.tex): for nonnegative weights with positive totals,
  `‖w/W - w'/W'‖₁ ≤ 2‖w - w'‖₁ / W`.
* Example `Two levels` (sec_normal.tex) for `m = 2`, `a = 1`, `b = 2`: `z = (5 - √17)/2` is the root in `(0,1)` of
  `(a-b)z^2 + (2b + ma - a)z - b = 0`, `c_f = b + (a-b) z = (√17 - 1)/2`, `z = 1/(1 + λa)` with `λ = m/c_f`,
  and the law `p_0 = z`, `p_k = p_1 r^{k-1}` with `p_1 = λaz/(1+λb)`, `r = λb/(1+λb)` has total mass 1 and mean `m`.
-/

open Finset

namespace P0089

/-! ## Lemma Degrees -/

/-- `L N i = Σ_{s=i}^{N-1} 1/(s+1)`. -/
noncomputable def L (N i : ℕ) : ℝ := ∑ s ∈ Ico i N, (1 : ℝ) / ((s : ℝ) + 1)

lemma L_succ (N i : ℕ) (hi : i ≤ N) : L (N + 1) i = L N i + 1 / ((N : ℝ) + 1) := by
  unfold L
  rw [sum_Ico_succ_top hi]

lemma L_self (N : ℕ) : L N N = 0 := by simp [L]

theorem sum_L (N : ℕ) : ∑ i ∈ range (N + 1), L N i = N := by
  induction N with
  | zero => simp [L]
  | succ N ih =>
    rw [sum_range_succ _ (N + 1), L_self, add_zero]
    have h : ∀ i ∈ range (N + 1), L (N + 1) i = L N i + 1 / ((N : ℝ) + 1) :=
      fun i hi => L_succ N i (Nat.lt_succ_iff.mp (mem_range.mp hi))
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    have key : ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) = 1 := mul_one_div_cancel hN
    rw [sum_congr rfl h, sum_add_distrib, ih, sum_const, card_range, nsmul_eq_mul]
    push_cast
    linear_combination key

theorem sum_L_sq (N : ℕ) :
    ∑ i ∈ range (N + 1), L N i ^ 2 = ∑ k ∈ range N, (2 * (k : ℝ) + 1) / ((k : ℝ) + 1) := by
  induction N with
  | zero => simp [L]
  | succ N ih =>
    rw [sum_range_succ _ (N + 1), L_self,
      sum_range_succ (fun k : ℕ => (2 * (k : ℝ) + 1) / ((k : ℝ) + 1)) N]
    have h : ∀ i ∈ range (N + 1), L (N + 1) i ^ 2 =
        L N i ^ 2 + (2 * (1 / ((N : ℝ) + 1))) * L N i + (1 / ((N : ℝ) + 1)) ^ 2 := by
      intro i hi
      rw [L_succ N i (Nat.lt_succ_iff.mp (mem_range.mp hi))]
      ring
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    rw [sum_congr rfl h, sum_add_distrib, sum_add_distrib, ← mul_sum, ih, sum_L, sum_const, card_range,
      nsmul_eq_mul]
    push_cast
    field_simp <;> ring

/-- The paper's form: `Σ_{s,t<n} min(s,t)/(st)`, shifted to `s, t ∈ [0, N)`. -/
noncomputable def g (s t : ℕ) : ℝ := min ((s : ℝ) + 1) ((t : ℝ) + 1) / (((s : ℝ) + 1) * ((t : ℝ) + 1))

theorem sum_min_eq (N : ℕ) :
    ∑ s ∈ range N, ∑ t ∈ range N, g s t = ∑ k ∈ range N, (2 * (k : ℝ) + 1) / ((k : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    have hrow : ∀ s ∈ range N, ∑ t ∈ range (N + 1), g s t = ∑ t ∈ range N, g s t + 1 / ((N : ℝ) + 1) := by
      intro s hs
      rw [sum_range_succ _ N]
      have hsN : (s : ℝ) + 1 ≤ (N : ℝ) + 1 := by
        have h1 : (s : ℝ) < N := by exact_mod_cast mem_range.mp hs
        linarith
      have hs0 : (s : ℝ) + 1 ≠ 0 := by positivity
      have e : g s N = 1 / ((N : ℝ) + 1) := by
        unfold g
        rw [min_eq_left hsN, div_mul_eq_div_div, div_self hs0]
      rw [e]
    have hcol : ∑ t ∈ range (N + 1), g N t = (N : ℝ) * (1 / ((N : ℝ) + 1)) + 1 / ((N : ℝ) + 1) := by
      rw [sum_range_succ _ N]
      have hc : ∀ t ∈ range N, g N t = 1 / ((N : ℝ) + 1) := by
        intro t ht
        have htN : (t : ℝ) + 1 ≤ (N : ℝ) + 1 := by
          have h1 : (t : ℝ) < N := by exact_mod_cast mem_range.mp ht
          linarith
        have ht0 : (t : ℝ) + 1 ≠ 0 := by positivity
        unfold g
        rw [min_eq_right htN, mul_comm, div_mul_eq_div_div, div_self ht0]
      have hd : g N N = 1 / ((N : ℝ) + 1) := by
        unfold g
        rw [min_self, div_mul_eq_div_div, div_self hN]
      rw [sum_congr rfl hc, sum_const, card_range, nsmul_eq_mul, hd]
    rw [sum_range_succ (fun s => ∑ t ∈ range (N + 1), g s t) N, sum_congr rfl hrow, sum_add_distrib, ih,
      sum_const, card_range, nsmul_eq_mul, hcol,
      sum_range_succ (fun k : ℕ => (2 * (k : ℝ) + 1) / ((k : ℝ) + 1)) N]
    field_simp <;> ring

/-- `Σ_{i ≤ n} L_i^2 = Σ_{s,t<n} min(s,t)/(st) = 2(n-1) - H_{n-1}`. -/
theorem sum_L_sq_eq (N : ℕ) :
    ∑ i ∈ range (N + 1), L N i ^ 2 = ∑ s ∈ range N, ∑ t ∈ range N, g s t ∧
    ∑ i ∈ range (N + 1), L N i ^ 2 = 2 * (N : ℝ) - ∑ k ∈ range N, 1 / ((k : ℝ) + 1) := by
  refine ⟨by rw [sum_L_sq, sum_min_eq], ?_⟩
  rw [sum_L_sq]
  have h : ∀ k ∈ range N, (2 * (k : ℝ) + 1) / ((k : ℝ) + 1) = 2 - 1 / ((k : ℝ) + 1) := by
    intro k _
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp <;> ring
  rw [sum_congr rfl h, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  ring

/-- The bound used in the proof of Lemma Degrees: `Σ_{i ≤ n} L_i^2 ≤ 2(n-1)`. -/
theorem sum_L_sq_le (N : ℕ) : ∑ i ∈ range (N + 1), L N i ^ 2 ≤ 2 * (N : ℝ) := by
  rw [(sum_L_sq_eq N).2]
  have : 0 ≤ ∑ k ∈ range N, 1 / ((k : ℝ) + 1) := sum_nonneg (fun k _ => by positivity)
  linarith

/-! ## The normalisation step of Lemma forcedS -/

theorem l1_normalise {ι : Type*} (S : Finset ι) (w w' : ι → ℝ) (hw' : ∀ i ∈ S, 0 ≤ w' i)
    (hW : 0 < ∑ j ∈ S, w j) (hW' : 0 < ∑ j ∈ S, w' j) :
    ∑ i ∈ S, |w i / (∑ j ∈ S, w j) - w' i / (∑ j ∈ S, w' j)| ≤
      2 * (∑ i ∈ S, |w i - w' i|) / ∑ j ∈ S, w j := by
  set W := ∑ j ∈ S, w j with hWdef
  set W' := ∑ j ∈ S, w' j with hW'def
  set A := ∑ i ∈ S, |w i - w' i| with hAdef
  have hW0 : W ≠ 0 := hW.ne'
  have hW'0 : W' ≠ 0 := hW'.ne'
  have key : ∀ i ∈ S, |w i / W - w' i / W'| ≤ |w i - w' i| / W + w' i * |1 / W - 1 / W'| := by
    intro i hi
    have e : w i / W - w' i / W' = (w i - w' i) / W + w' i * (1 / W - 1 / W') := by ring
    rw [e]
    calc |(w i - w' i) / W + w' i * (1 / W - 1 / W')|
        ≤ |(w i - w' i) / W| + |w' i * (1 / W - 1 / W')| := abs_add_le _ _
      _ = |w i - w' i| / W + w' i * |1 / W - 1 / W'| := by
        rw [abs_div, abs_of_pos hW, abs_mul, abs_of_nonneg (hw' i hi)]
  have h1 := sum_le_sum key
  rw [sum_add_distrib, ← sum_div, ← sum_mul, ← hAdef, ← hW'def] at h1
  have h2 : W' * |1 / W - 1 / W'| = |W' - W| / W := by
    have e : 1 / W - 1 / W' = (W' - W) / (W * W') := by
      rw [div_sub_div _ _ hW0 hW'0]
      ring
    rw [e, abs_div, abs_of_pos (mul_pos hW hW'), mul_div_assoc',
      div_eq_div_iff (mul_ne_zero hW0 hW'0) hW0]
    ring
  have h3 : |W' - W| ≤ A := by
    have e : W' - W = ∑ i ∈ S, (w' i - w i) := by rw [sum_sub_distrib, hW'def, hWdef]
    rw [e]
    calc |∑ i ∈ S, (w' i - w i)| ≤ ∑ i ∈ S, |w' i - w i| := abs_sum_le_sum_abs _ _
      _ = A := sum_congr rfl (fun i _ => abs_sub_comm _ _)
  have h4 : |W' - W| / W ≤ A / W := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hW.le)
  have h5 : 2 * A / W = A / W + A / W := by ring
  rw [h2] at h1
  rw [h5]
  linarith

/-! ## Example Two levels, `m = 2`, `a = 1`, `b = 2` -/

theorem two_levels :
    let s := Real.sqrt 17
    let z := (5 - s) / 2
    let c := (s - 1) / 2
    let lam := 2 / c
    let p1 := lam * 1 * z / (1 + lam * 2)
    let r := lam * 2 / (1 + lam * 2)
    ((1 - 2) * z ^ 2 + (2 * 2 + 2 * 1 - 1) * z - 2 = 0) ∧ 0 < z ∧ z < 1 ∧
    c = 2 + (1 - 2) * z ∧ z = 1 / (1 + lam * 1) ∧
    0 ≤ r ∧ r < 1 ∧ z + p1 / (1 - r) = 1 ∧ p1 / (1 - r) ^ 2 = 2 := by
  intro s z c lam p1 r
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 17
  have hs2 : s ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs4 : 4 < s := by nlinarith
  have hs5 : s < 5 := by nlinarith
  have hc : 0 < c := by simp only [c]; linarith
  have hc0 : c ≠ 0 := hc.ne'
  have hlam : 0 < lam := div_pos (by norm_num) hc
  have hd : 0 < 1 + lam * 2 := by linarith
  have hd0 : 1 + lam * 2 ≠ 0 := hd.ne'
  have hr1 : 1 - r = 1 / (1 + lam * 2) := by
    simp only [r]
    field_simp <;> ring
  -- c^2 + c = 4, z (c + 2) = c and z = 2 - c: everything below reduces to these
  have hcc : c ^ 2 + c = 4 := by simp only [c]; linear_combination hs2 / 4
  have hzc : z * (c + 2) = c := by simp only [z, c]; linear_combination (-1 / 4 : ℝ) * hs2
  have hz : z = 2 - c := by simp only [z, c]; ring
  have hzc4 : z * (c + 4) = c ^ 2 := by rw [hz]; linear_combination (-2 : ℝ) * hcc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [z]; linear_combination (-1 / 4 : ℝ) * hs2
  · simp only [z]; linarith
  · simp only [z]; linarith
  · rw [hz]; ring
  · have hne : 1 + lam * 1 ≠ 0 := (by linarith : (0 : ℝ) < 1 + lam * 1).ne'
    rw [eq_div_iff hne]
    have e : z * (1 + lam * 1) = z * (c + 2) / c := by simp only [lam]; field_simp <;> ring
    rw [e, hzc, div_self hc0]
  · exact div_nonneg (by linarith) hd.le
  · exact (div_lt_one hd).mpr (by linarith)
  · rw [hr1]
    have hp : p1 / (1 / (1 + lam * 2)) = lam * 1 * z := by simp only [p1]; field_simp <;> ring
    have e : z + lam * 1 * z = z * (c + 2) / c := by simp only [lam]; field_simp <;> ring
    rw [hp, e, hzc, div_self hc0]
  · rw [hr1]
    have hp : p1 / (1 / (1 + lam * 2)) ^ 2 = lam * 1 * z * (1 + lam * 2) := by
      simp only [p1]; field_simp <;> ring
    have e : lam * 1 * z * (1 + lam * 2) = 2 * (z * (c + 4)) / c ^ 2 := by
      simp only [lam]; field_simp <;> ring
    rw [hp, e, hzc4, mul_div_assoc, div_self (pow_ne_zero 2 hc0), mul_one]

end P0089

#print axioms P0089.sum_L
#print axioms P0089.sum_L_sq_eq
#print axioms P0089.sum_L_sq_le
#print axioms P0089.l1_normalise
#print axioms P0089.two_levels
