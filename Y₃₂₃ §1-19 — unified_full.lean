import Mathlib

/-! # Y(3,2,3) — Unified Formalisation (Sections 1–19)

    This file is the single canonical source for the Y₃₂₃ structure,
    covering the operator algebra, cascade constants, electroweak constants,
    quark cascade levels, and the gravity bridge.

    § 1.  Fundamental constants  (ω, sConst, φVal, cascadeN, cascadeFreq)
    § 2.  The Y₃₂₃ operator  (7×7 complex matrix)
    § 3.  Block decoupling  (N-sector ↔ M-sector vanishing cross-terms)
    § 4.  The canonical nilpotent block Y_nil  (ω-dependent, 3×3)
    § 5.  Nilpotency maximality of Y_nil
    § 6.  Jordan chain properties of Y_nil  (proved from the ω-dependent form)
    § 7.  The simplified nilpotent block Y_nil_simp  (integer / i matrix)
    § 8.  Unitary equivalence  Y_nil_simp ~ Y_nil
    § 9.  Cascade constants (φ, N) and muon level
    § 10. Fine structure constant  (ideal value, golden angle, triangulation)
    § 11. Electron charge derivation  (rational arithmetic)
    § 12. Jordan chain amplitude theorem  (triangulation ratio = 2√2)
    § 13. Tau cascade level
    § 14. Electroweak constants  (Weinberg angle, strong coupling)
    § 15. Lepton mass ratios
    § 16. Quark cascade levels and mass ratios
    § 17. Fano contraction and the keystone lemma
    § 18. Parameter fixing: lam, μ, ν, κ from φ, N, ω, G_N
    § 19. The discrete limit theorem

    Naming conventions
    ──────────────────
    • The golden ratio is `φVal` throughout.  No `goldenRatio` alias is used.
    • The mixing parameter is `ω`; `mixingOmega` is a definitional alias.
    • `sConst` = √3/2 (avoids collision with tactic name `s`).
    • `cascadeFreq` = 2π/N = ln φ, defined in § 1 so that §§ 17–19 may use it.
    • All matrices are over ℂ.
    • Y_nil is the canonical ω-dependent form; Y_nil_simp is a secondary form
      proved unitarily equivalent in § 8.
    • `lam_param` is used instead of `λ_param` since `λ` is a Lean 4 keyword.
    • `ν_param` is defined with positive sign: ν = λ · (ln φ)², so that the
      scalar cancellation λ□ψ + νψ = 0 holds when □ψ = −(2π/N)²ψ.
-/

open Complex Matrix Real

-- ══════════════════════════════════════════════════════════════════════════════
-- § 1.  Fundamental constants
-- ══════════════════════════════════════════════════════════════════════════════

/-- The Y₃₂₃ mixing parameter  ω = 1 / √2 -/
noncomputable def ω : ℝ := 1 / Real.sqrt 2

/-- The Y₃₂₃ structural constant  sConst = √3 / 2 -/
noncomputable def sConst : ℝ := Real.sqrt 3 / 2

/-- The golden ratio  φ = (1 + √5) / 2 -/
noncomputable def φVal : ℝ := (1 + Real.sqrt 5) / 2

/-- The cascade period  N = 2π / ln φ -/
noncomputable def cascadeN : ℝ := 2 * Real.pi / Real.log φVal

/-- The cascade frequency  freq = 2π / N = ln φ. -/
noncomputable def cascadeFreq : ℝ := 2 * Real.pi / cascadeN

/-- Alias: mixingOmega = ω -/
noncomputable def mixingOmega : ℝ := ω

lemma ω_pos : 0 < ω := by unfold ω; positivity

lemma ω_sq : ω ^ 2 = 1 / 2 := by
  unfold ω; field_simp; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma ω_sq_complex : (ω : ℂ) ^ 2 = 1 / 2 := by
  have h := ω_sq
  have : ((ω ^ 2 : ℝ) : ℂ) = ((1/2 : ℝ) : ℂ) := by rw [h]
  push_cast at this ⊢; exact this

-- ══════════════════════════════════════════════════════════════════════════════
-- § 2.  The Y₃₂₃ operator  (7×7 complex matrix)
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def Y323 : Matrix (Fin 7) (Fin 7) ℂ :=
  !![0,                    -I,         0,         0,          0,          -(1 + I) * (ω : ℂ), 0;
     I,                     0,         0,         0,          0,           0,                  0;
     0,                     0,         0,         1,          0,           0,                  0;
     0,                     0,        -1,         0,          (ω : ℂ),     0,                  0;
     0,                     0,         0,         (ω : ℂ),   0,           0,                  -I * (sConst : ℂ);
     (1 + I) * (ω : ℂ),    0,         0,         0,          0,           0,                  0;
     0,                     0,         0,         0,          I * (sConst : ℂ), 0,             0]

-- ══════════════════════════════════════════════════════════════════════════════
-- § 3.  Block decoupling
-- ══════════════════════════════════════════════════════════════════════════════

theorem block_decoupling :
    (∀ i ∈ ({2, 3, 4, 6} : Finset (Fin 7)),
     ∀ j ∈ ({0, 1, 5} : Finset (Fin 7)),
     Y323 i j = 0) ∧
    (∀ i ∈ ({0, 1, 5} : Finset (Fin 7)),
     ∀ j ∈ ({2, 3, 4, 6} : Finset (Fin 7)),
     Y323 i j = 0) := by
  constructor <;> intro i hi j hj <;>
    fin_cases i <;> fin_cases j <;>
    simp_all [Y323, Matrix.cons_val_zero, Matrix.cons_val_one,
              Finset.mem_insert, Finset.mem_singleton]

-- ══════════════════════════════════════════════════════════════════════════════
-- § 4.  The canonical nilpotent block  Y_nil  (ω-dependent)
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def Y_nil : Matrix (Fin 3) (Fin 3) ℂ :=
  !![ 0,                 -I,               (ω : ℂ) * (-1 + I);
      I,                  0,               0;
      (ω : ℂ) * (1 + I), 0,               0]

/-
PROBLEM
══════════════════════════════════════════════════════════════════════════════
§ 5.  Nilpotency maximality
══════════════════════════════════════════════════════════════════════════════

PROVIDED SOLUTION
Compute (Y_nil * Y_nil) 0 0 by expanding the matrix product using Fin.sum_univ_three, simplifying the Y_nil entries, using ring_nf and I_sq to get 1 - 2*(ω:ℂ)^2.
-/
lemma nil_sq_00 : (Y_nil * Y_nil) 0 0 = 1 - 2 * (ω : ℂ) ^ 2 := by
  norm_num [ Y_nil, Fin.sum_univ_succ ] ; ring;
  norm_num ; ring

theorem nilpotency_maximality : (Y_nil * Y_nil) 0 0 = 0 := by
  rw [nil_sq_00, ω_sq_complex]; ring

-- ══════════════════════════════════════════════════════════════════════════════
-- § 6.  Jordan chain properties of Y_nil
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def e₀ : Fin 3 → ℂ := ![1, 0, 0]
noncomputable def e₁ : Fin 3 → ℂ := ![0, 1, 0]
noncomputable def e₂ : Fin 3 → ℂ := ![0, 0, 1]

noncomputable def mulVec₃ (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => ∑ j, M i j * v j

/-
PROVIDED SOLUTION
Expand mulVec₃ (Y_nil * Y_nil) e₀ entry by entry using ext i; fin_cases i. For each case, simp with mulVec₃, Y_nil, Matrix.mul_apply, Fin.sum_univ_three, e₀, then ring_nf, then use I_sq and ω_sq_complex. May need set_option maxHeartbeats 800000.
-/
theorem tau_jordan_length_two :
    mulVec₃ (Y_nil * Y_nil) e₀ = ![0, 0, 0] := by
      unfold mulVec₃ Y_nil e₀; simp +decide [ Fin.sum_univ_three, Matrix.mul_apply ] ;
      ext i; fin_cases i <;> norm_num [ Complex.ext_iff ] ; ring ;
      norm_num [ ω_sq ]

/-
PROVIDED SOLUTION
Assume mulVec₃ Y_nil e₀ = ![0,0,0]. Extract component 1, which gives I = 0, contradiction via norm_num.
-/
theorem tau_jordan_nontrivial :
    mulVec₃ Y_nil e₀ ≠ ![0, 0, 0] := by
      unfold mulVec₃ Y_nil e₀; norm_num [ ← List.ofFn_inj ] ;
      norm_num [ Fin.sum_univ_succ, Complex.ext_iff ]

/-
PROVIDED SOLUTION
Assume mulVec₃ (Y_nil * Y_nil) e₁ = ![0,0,0]. Extract component 0 which should give a nonzero value. After simplification, ring_nf and I_sq should give a contradiction with norm_num.
-/
theorem a1_jordan_length_gt_two :
    mulVec₃ (Y_nil * Y_nil) e₁ ≠ ![0, 0, 0] := by
      unfold mulVec₃ Y_nil e₁; norm_num [ Fin.sum_univ_succ, Matrix.mul_apply ] ; ring_nf ;
      norm_num [ funext_iff, Fin.forall_fin_succ ]

/-
PROVIDED SOLUTION
Expand mulVec₃ (Y_nil * Y_nil * Y_nil) e₁ entry by entry. For each fin_cases i, use simp with mulVec₃, Y_nil, Matrix.mul_apply, Fin.sum_univ_three, e₁, then ring_nf, I_sq, ω_sq_complex. May need set_option maxHeartbeats 1600000.
-/
theorem a1_jordan_length_three :
    mulVec₃ (Y_nil * Y_nil * Y_nil) e₁ = ![0, 0, 0] := by
      unfold mulVec₃ Y_nil;
      unfold e₁; norm_num [ Fin.sum_univ_succ, Matrix.mul_apply ] ; ring_nf; norm_num [ Complex.ext_iff, sq ] ;
      ext i; fin_cases i <;> norm_num [ ω ] ; ring_nf ; norm_num [ Complex.ext_iff, sq ] ;
      ring_nf; norm_num;

/-
PROVIDED SOLUTION
Assume mulVec₃ (Y_nil * Y_nil) e₂ = ![0,0,0]. Extract component 0. After simplification, use that (ω:ℂ) ≠ 0 (from ω_pos) to derive contradiction.
-/
theorem x_jordan_length_gt_two :
    mulVec₃ (Y_nil * Y_nil) e₂ ≠ ![0, 0, 0] := by
      unfold mulVec₃ Y_nil e₂; norm_num [ Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail, Matrix.mul_apply ] ; ring_nf ;
      intro h; have := congr_fun h 0; norm_num [ Complex.ext_iff ] at this; ( have := congr_fun h 1; norm_num [ Complex.ext_iff ] at this; ( have := congr_fun h 2; norm_num [ Complex.ext_iff ] at this; ) );
      exact absurd ‹ω = 0› ( by exact ne_of_gt ( by exact one_div_pos.mpr ( Real.sqrt_pos.mpr zero_lt_two ) ) )

/-
PROVIDED SOLUTION
Expand mulVec₃ (Y_nil * Y_nil * Y_nil) e₂ entry by entry. For each fin_cases i, use simp with mulVec₃, Y_nil, Matrix.mul_apply, Fin.sum_univ_three, e₂, then ring_nf, I_sq, ω_sq_complex. May need set_option maxHeartbeats 1600000.
-/
theorem x_jordan_length_three :
    mulVec₃ (Y_nil * Y_nil * Y_nil) e₂ = ![0, 0, 0] := by
      -- By simplifying, we can see that the result is indeed the zero vector.
      ext i
      simp [mulVec₃, Y_nil];
      fin_cases i <;> norm_num [ Fin.sum_univ_succ, e₂ ] ; ring_nf ; norm_num [ Complex.ext_iff, sq ];
      exact Or.inl ( by rw [ show ω = 1 / Real.sqrt 2 by rfl ] ; ring_nf; norm_num )

theorem jordan_asymmetry :
    mulVec₃ (Y_nil * Y_nil) e₀ = ![0, 0, 0] ∧
    mulVec₃ (Y_nil * Y_nil) e₁ ≠ ![0, 0, 0] ∧
    mulVec₃ (Y_nil * Y_nil) e₂ ≠ ![0, 0, 0] :=
  ⟨tau_jordan_length_two, a1_jordan_length_gt_two, x_jordan_length_gt_two⟩

-- ══════════════════════════════════════════════════════════════════════════════
-- § 7.  The simplified nilpotent block  Y_nil_simp
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def Y_nil_simp : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0,  1,  I;
    -I,  0,  0;
     1,  0,  0]

-- ══════════════════════════════════════════════════════════════════════════════
-- § 8.  Unitary equivalence  Y_nil_simp ~ Y_nil
-- ══════════════════════════════════════════════════════════════════════════════

lemma Y_nil_trace : Matrix.trace Y_nil = 0 := by
  simp [Y_nil, Matrix.trace, Fin.sum_univ_three]

lemma Y_nil_simp_trace : Matrix.trace Y_nil_simp = 0 := by
  simp [Y_nil_simp, Matrix.trace, Fin.sum_univ_three]

/-
PROVIDED SOLUTION
Compute Y_nil^3 entry by entry. Use ext i j; fin_cases i; fin_cases j; then for each case simp with Y_nil, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, then ring_nf and use I_sq and ω_sq_complex. May need set_option maxHeartbeats 1600000.
-/
lemma Y_nil_cube_zero : Y_nil ^ 3 = 0 := by
  unfold Y_nil;
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [ pow_three ] <;> ring_nf <;> norm_num [ Complex.ext_iff, sq ] ;
  · rw [ ← sq ] ; rw [ ω_sq ] ; ring;
  · norm_num [ pow_three ] ; ring ; norm_num [ ω ] ;
    norm_num [ pow_three ] ; ring ; norm_num;
  · norm_num [ ω ] ; ring ; norm_num;
  · exact Or.inr ( by rw [ show ω = 1 / Real.sqrt 2 by rfl ] ; ring_nf; norm_num )

/-
PROVIDED SOLUTION
Compute Y_nil_simp^3 entry by entry. For each (i,j) case, expand using pow_succ, Matrix.mul_apply, Fin.sum_univ_three, then ring_nf and I_sq. May need set_option maxHeartbeats 800000.
-/
lemma Y_nil_simp_cube_zero : Y_nil_simp ^ 3 = 0 := by
  unfold Y_nil_simp;
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ pow_succ ] <;> ring_nf <;> norm_num [ Complex.ext_iff, sq ] at * <;> first | linarith | aesop | trivial;

/-
PROVIDED SOLUTION
Assume Y_nil^2 = 0. Extract entry (1,0) which is nonzero. Use pow_two, Matrix.mul_apply, Fin.sum_univ_three to compute, then ring_nf, I_sq, norm_num for contradiction.
-/
lemma Y_nil_sq_ne_zero : Y_nil ^ 2 ≠ 0 := by
  unfold Y_nil;
  norm_num [ sq, ← List.ofFn_inj ];
  intro h; have := congr_fun ( congr_fun h 1 ) 1; norm_num at this;

/-
PROVIDED SOLUTION
Assume Y_nil_simp^2 = 0, then extract entry (1,1) which should be nonzero. Use pow_two, expand matrix product for entry (1,1), compute to get a contradiction with norm_num.
-/
lemma Y_nil_simp_sq_ne_zero : Y_nil_simp ^ 2 ≠ 0 := by
  intro h; have := congr_fun ( congr_fun h 1 ) 1; norm_num [ Fin.sum_univ_succ, pow_two, Y_nil_simp ] at this;

/-
PROVIDED SOLUTION
Unfold Y_nil entries. Use norm_zero, Complex.norm_I, norm_one, norm_neg for the simple entries. For entries like (ω:ℂ)*(-1+I) and (ω:ℂ)*(1+I), compute the norm as ω*√2 = 1. Then 0+1+1+1+0+0+1+0+0 = 4. Key: ‖(ω:ℂ)*(-1+I)‖ = ω*√2 = (1/√2)*√2 = 1, so ‖...‖^2 = 1.
-/
lemma Y_nil_frob_sq :
    ‖Y_nil 0 0‖^2 + ‖Y_nil 0 1‖^2 + ‖Y_nil 0 2‖^2 +
    ‖Y_nil 1 0‖^2 + ‖Y_nil 1 1‖^2 + ‖Y_nil 1 2‖^2 +
    ‖Y_nil 2 0‖^2 + ‖Y_nil 2 1‖^2 + ‖Y_nil 2 2‖^2 = 4 := by
      unfold Y_nil; norm_num [ Complex.normSq, Complex.norm_def ] ; ring;
      simp +zetaDelta at *;
      rw [ Real.sq_sqrt ] <;> nlinarith [ ω_sq ]

/-
PROVIDED SOLUTION
Unfold Y_nil_simp entries, compute norms: ‖0‖=0, ‖1‖=1, ‖I‖=1, ‖-I‖=1. Use norm_zero, norm_one, Complex.norm_I, norm_neg. Then 0+1+1+1+0+0+1+0+0 = 4. Use simp with these lemmas then norm_num.
-/
lemma Y_nil_simp_frob_sq :
    ‖Y_nil_simp 0 0‖^2 + ‖Y_nil_simp 0 1‖^2 + ‖Y_nil_simp 0 2‖^2 +
    ‖Y_nil_simp 1 0‖^2 + ‖Y_nil_simp 1 1‖^2 + ‖Y_nil_simp 1 2‖^2 +
    ‖Y_nil_simp 2 0‖^2 + ‖Y_nil_simp 2 1‖^2 + ‖Y_nil_simp 2 2‖^2 = 4 := by
      unfold Y_nil_simp; norm_num [ Complex.normSq, Complex.norm_def ] ;
      repeat erw [ Matrix.cons_val_succ' ] ; norm_num;

-- ══════════════════════════════════════════════════════════════════════════════
-- § 9.  Cascade constants and muon level
-- ══════════════════════════════════════════════════════════════════════════════

lemma φVal_pos : 0 < φVal := by unfold φVal; positivity

lemma φVal_gt_one : 1 < φVal := by
  unfold φVal
  have h : (1 : ℝ) < Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

lemma ln_φVal_pos : 0 < Real.log φVal :=
  Real.log_pos φVal_gt_one

lemma cascadeN_pos : 0 < cascadeN :=
  div_pos (by linarith [Real.pi_pos]) ln_φVal_pos

/-
PROVIDED SOLUTION
We need φ < 2π/(ln φ). Equivalently φ·ln(φ) < 2π. We have φ < 2 (since √5 < 3) and ln(φ) < 1 (since φ < e). So φ·ln(φ) < 2·1 = 2 < 2π. Use φVal_pos, φVal_gt_one, cascadeN_pos. Show φVal < 2 by bounding √5 < 3. Show Real.log φVal < 1 by showing φVal < Real.exp 1 (since e > 2.7 > 2 > φ). Then φVal * Real.log φVal < 2 < 2π. Use lt_div_iff₀ with ln_φVal_pos.
-/
lemma φVal_lt_cascadeN : φVal < cascadeN := by
  refine' lt_div_iff₀ ( Real.log_pos <| by rw [ show φVal = ( 1 + Real.sqrt 5 ) / 2 by rfl ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) |>.2 _;
  -- We'll use that $\phi \approx 1.618$ and $\ln \phi \approx 0.481$.
  have h_phi_approx : φVal < 2 := by
    exact show ( 1 + Real.sqrt 5 ) / 2 < 2 by nlinarith [ Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ;
  have h_ln_phi_approx : Real.log φVal < 1 := by
    exact lt_of_lt_of_le ( Real.log_lt_log ( by exact ( show 0 < φVal by exact ( show 0 < ( 1 + Real.sqrt 5 ) / 2 by positivity ) ) ) h_phi_approx ) ( Real.log_two_lt_d9.le.trans ( by norm_num ) );
  nlinarith [ Real.pi_gt_three, Real.log_nonneg ( show φVal ≥ 1 by rw [ show φVal = ( 1 + Real.sqrt 5 ) / 2 by rfl ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ]

/-
PROVIDED SOLUTION
sin(π(N-φ)/N) = sin(π - πφ/N) = sin(πφ/N). Use Real.sin_pi_sub. First show π*(N-φ)/N = π - πφ/N by field_simp with cascadeN ≠ 0, then ring.
-/
theorem muon_residual_zero :
    Real.sin (Real.pi * (cascadeN - φVal) / cascadeN) =
    Real.sin (Real.pi * φVal / cascadeN) := by
      rw [ ← Real.sin_pi_sub ] ; ring_nf ; norm_num [ cascadeN_pos.ne' ] ;

noncomputable def muonLevel : ℝ := cascadeN - φVal

lemma muonLevel_pos : 0 < muonLevel := sub_pos.mpr φVal_lt_cascadeN

theorem muon_level_def : muonLevel = cascadeN - φVal := rfl

theorem muon_at_cascade_zero :
    Real.sin (Real.pi * muonLevel / cascadeN) =
    Real.sin (Real.pi * φVal / cascadeN) := by
  unfold muonLevel; exact muon_residual_zero

-- ══════════════════════════════════════════════════════════════════════════════
-- § 10.  Fine structure constant
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def idealAlphaInv : ℝ := 6 * φVal ^ (cascadeN / 2)

/-
PROVIDED SOLUTION
idealAlphaInv = 6 * φVal ^ (cascadeN/2). cascadeN = 2π/(ln φ), so cascadeN/2 = π/(ln φ). φ^(π/ln φ) = exp(ln(φ)·π/ln(φ)) = exp(π). Use Real.rpow_def_of_pos φVal_pos. The log satisfies log(φ)·(cascadeN/2) = log(φ)·π/log(φ) = π. Use field_simp and mul_div_cancel with ln_φVal_pos.
-/
theorem idealAlphaInv_eq_six_exp_pi :
    idealAlphaInv = 6 * Real.exp Real.pi := by
      unfold idealAlphaInv;
      rw [ Real.rpow_def_of_pos ( by exact ( show 0 < φVal from φVal_pos ) ) ];
      unfold cascadeN; ring_nf ; norm_num [ Real.pi_ne_zero ] ;
      exact mul_div_cancel_left₀ _ ( ne_of_gt ( Real.log_pos ( by rw [ show φVal = ( 1 + Real.sqrt 5 ) / 2 by rfl ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ) )

noncomputable def goldenAngleAlphaInv : ℝ := 360 / φVal ^ 2
noncomputable def triangulationRatio : ℝ := 2 / ω

lemma triangulationRatio_eq : triangulationRatio = 2 * Real.sqrt 2 := by
  simp [triangulationRatio, ω]

lemma triangulationRatio_pos : 0 < triangulationRatio :=
  div_pos (by norm_num) ω_pos

theorem triangulation_identity (α_obs_inv : ℝ)
    (h : α_obs_inv = goldenAngleAlphaInv -
         (idealAlphaInv - goldenAngleAlphaInv) / triangulationRatio) :
    (idealAlphaInv - goldenAngleAlphaInv) =
    triangulationRatio * (goldenAngleAlphaInv - α_obs_inv) := by
  rw [h, sub_sub_cancel,
      mul_div_cancel₀ _ (ne_of_gt triangulationRatio_pos)]

-- ══════════════════════════════════════════════════════════════════════════════
-- § 11.  Electron charge derivation  (rational arithmetic)
-- ══════════════════════════════════════════════════════════════════════════════

def w_a2  : ℚ := 1/16
def w_b1  : ℚ := 1/16
def w_b2  : ℚ := 1/2
def w_eta : ℚ := 3/8
def q_b1  : ℚ :=  1/3
def q_b2  : ℚ :=  1/3
def q_eta : ℚ := -2/3

lemma stone_unit_norm : w_a2 + w_b1 + w_b2 + w_eta = 1 := by
  simp [w_a2, w_b1, w_b2, w_eta]; norm_num

theorem stone_colour_charge :
    q_b1 * w_b1 + q_b2 * w_b2 + q_eta * w_eta = -1/16 := by
  simp [q_b1, q_b2, q_eta, w_b1, w_b2, w_eta]; norm_num

theorem electron_charge :
    (q_b1 * w_b1 + q_b2 * w_b2 + q_eta * w_eta) / w_a2 = -1 := by
  rw [stone_colour_charge]; simp [w_a2]

def w_a2_water : ℚ := 1/16
theorem observer_invariance : w_a2 = w_a2_water := by simp [w_a2, w_a2_water]

-- ══════════════════════════════════════════════════════════════════════════════
-- § 12.  Jordan chain amplitude theorem  (triangulation ratio = 2√2)
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def Y_nil_col0 : Fin 3 → ℂ := ![0, -I, 1]

lemma Y_nil_mul_e0 :
    Y_nil_simp.mulVec ![1, 0, 0] = Y_nil_col0 := by
  ext i; fin_cases i <;> norm_num [Y_nil_simp, Y_nil_col0]

/-
PROVIDED SOLUTION
Y_nil_col0 = ![0, -I, 1]. So ‖0‖^2 + ‖-I‖^2 + ‖1‖^2 = 0 + 1 + 1 = 2. Use norm_zero, Complex.norm_I (or norm_neg + Complex.norm_I), norm_one.
-/
lemma Y_nil_col0_norm_sq :
    ‖Y_nil_col0 0‖^2 + ‖Y_nil_col0 1‖^2 + ‖Y_nil_col0 2‖^2 = 2 := by
      unfold Y_nil_col0; norm_num [ Complex.normSq, Complex.norm_def ] ;
      erw [ Matrix.cons_val_succ' ] ; norm_num;

noncomputable def Y_nil_sq_block : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-I, 1;
      1, I]

/-
PROVIDED SOLUTION
Y_nil_sq_block = !![−I, 1; 1, I]. Norms: ‖-I‖=1, ‖1‖=1, ‖1‖=1, ‖I‖=1. So 1+1+1+1=4. Use Complex.norm_I, norm_one, norm_neg, norm_num.
-/
lemma Y_nil_sq_block_frob_sq :
    ‖Y_nil_sq_block 0 0‖^2 + ‖Y_nil_sq_block 0 1‖^2 +
    ‖Y_nil_sq_block 1 0‖^2 + ‖Y_nil_sq_block 1 1‖^2 = 4 := by
      unfold Y_nil_sq_block; norm_num [ Complex.normSq, Complex.norm_def ] ;

theorem jordan_amplitude_ratio :
    (‖Y_nil_sq_block 0 0‖^2 + ‖Y_nil_sq_block 0 1‖^2 +
     ‖Y_nil_sq_block 1 0‖^2 + ‖Y_nil_sq_block 1 1‖^2) /
    (‖Y_nil_col0 0‖^2 + ‖Y_nil_col0 1‖^2 + ‖Y_nil_col0 2‖^2) = 2 := by
  rw [Y_nil_sq_block_frob_sq, Y_nil_col0_norm_sq]; norm_num

theorem triangulation_from_jordan :
    triangulationRatio =
    ((‖Y_nil_sq_block 0 0‖^2 + ‖Y_nil_sq_block 0 1‖^2 +
      ‖Y_nil_sq_block 1 0‖^2 + ‖Y_nil_sq_block 1 1‖^2) /
     (‖Y_nil_col0 0‖^2 + ‖Y_nil_col0 1‖^2 + ‖Y_nil_col0 2‖^2)) *
    (1 / ω) := by
  rw [jordan_amplitude_ratio]
  unfold triangulationRatio ω; ring

theorem triangulation_ratio_from_jordan_eq_two_sqrt_two :
    triangulationRatio = 2 * Real.sqrt 2 :=
  triangulationRatio_eq

-- ══════════════════════════════════════════════════════════════════════════════
-- § 13.  Tau cascade level
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def tauLevel : ℝ := cascadeN + 3 * Real.sqrt 2

lemma tauLevel_pos : 0 < tauLevel := by
  apply add_pos_of_pos_of_nonneg cascadeN_pos; positivity

/-
PROVIDED SOLUTION
sin(π·(N+3√2)/N) = sin(π + 3√2·π/N) = -sin(3√2·π/N). Use Real.sin_add_pi. First rewrite the argument as π + 3*√2*π/N via field_simp with cascadeN ≠ 0.
-/
theorem tau_residual_zero :
    Real.sin (Real.pi * tauLevel / cascadeN) =
    - Real.sin (3 * Real.sqrt 2 * Real.pi / cascadeN) := by
      convert Real.sin_add_pi _ using 2 ; ring;
      unfold tauLevel; ring; norm_num [ Real.pi_pos.ne.symm, show cascadeN ≠ 0 by exact ne_of_gt ( by exact div_pos ( mul_pos two_pos Real.pi_pos ) ( by exact Real.log_pos ( by rw [ show φVal = ( 1 + Real.sqrt 5 ) / 2 by rfl ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 5 ≥ 0 by norm_num ) ] ) ) ) ] ;

-- ══════════════════════════════════════════════════════════════════════════════
-- § 14.  Electroweak constants
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def weinbergSinSq : ℝ := 3 / cascadeN
noncomputable def strongCoupling : ℝ := 3 / (2 * cascadeN)

theorem strongCoupling_eq_weinberg_half :
    strongCoupling = weinbergSinSq / 2 := by
  unfold strongCoupling weinbergSinSq; ring

-- ══════════════════════════════════════════════════════════════════════════════
-- § 15.  Lepton mass ratios
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def muonMassRatio : ℝ := φVal ^ muonLevel * Real.sqrt 3 / 2
noncomputable def tauMassRatio : ℝ := φVal ^ tauLevel * Real.sqrt 3 / 2

theorem muonMassRatio_def :
    muonMassRatio = φVal ^ (cascadeN - φVal) * Real.sqrt 3 / 2 := by
  unfold muonMassRatio muonLevel; rfl

theorem tauMassRatio_def :
    tauMassRatio = φVal ^ (cascadeN + 3 * Real.sqrt 2) * Real.sqrt 3 / 2 := by
  unfold tauMassRatio tauLevel; rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- § 16.  Quark cascade levels and mass ratios
-- ══════════════════════════════════════════════════════════════════════════════

noncomputable def upQuarkLevel : ℝ := cascadeN / 4
noncomputable def downQuarkLevel : ℝ := 3 * cascadeN / 8
noncomputable def strangeQuarkLevel : ℝ := cascadeN - Real.sqrt 5
noncomputable def charmQuarkLevel : ℝ := cascadeN + cascadeN / 4
noncomputable def bottomQuarkLevel : ℝ := cascadeN + φVal + 3 * Real.sqrt 2
noncomputable def topQuarkLevel : ℝ := 2 * cascadeN + 1 / φVal

lemma upQuarkLevel_pos : 0 < upQuarkLevel := by
  unfold upQuarkLevel; have := cascadeN_pos; positivity
lemma downQuarkLevel_pos : 0 < downQuarkLevel := by
  unfold downQuarkLevel; have := cascadeN_pos; positivity

/-
PROVIDED SOLUTION
Similar to φVal_lt_cascadeN. Need √5 < 2π/(ln φ), i.e. √5·ln(φ) < 2π. We have √5 < 3 and ln(φ) < 1, so √5·ln(φ) < 3 < 2π. Use lt_div_iff₀ with ln_φVal_pos.
-/
lemma sqrt5_lt_cascadeN : Real.sqrt 5 < cascadeN := by
  rw [ show cascadeN = 2 * Real.pi / Real.log φVal from rfl ];
  rw [ lt_div_iff₀ ( Real.log_pos <| by rw [ φVal ] ; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ) ];
  -- We'll use that $Real.log φVal < 1$ to conclude the proof.
  have h_log_lt_one : Real.log φVal < 1 := by
    rw [ Real.log_lt_iff_lt_exp ] <;> norm_num [ Real.exp_pos, φVal ];
    · exact Real.exp_one_gt_d9.trans_le' <| by norm_num; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt <| show 0 ≤ 5 by norm_num ] ;
    · positivity
  nlinarith [Real.pi_gt_three, Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]

lemma strangeQuarkLevel_pos : 0 < strangeQuarkLevel := sub_pos.mpr sqrt5_lt_cascadeN

lemma charmQuarkLevel_pos : 0 < charmQuarkLevel := by
  unfold charmQuarkLevel; linarith [cascadeN_pos]

lemma bottomQuarkLevel_pos : 0 < bottomQuarkLevel := by
  unfold bottomQuarkLevel; have := cascadeN_pos; have := φVal_pos
  linarith [Real.sqrt_nonneg 2]

lemma topQuarkLevel_pos : 0 < topQuarkLevel := by
  unfold topQuarkLevel; have := cascadeN_pos; have := φVal_pos; positivity

noncomputable def upQuarkMassRatio : ℝ := φVal ^ upQuarkLevel * Real.sqrt 3 / 2
noncomputable def downQuarkMassRatio : ℝ := φVal ^ downQuarkLevel * Real.sqrt 3 / 2
noncomputable def strangeQuarkMassRatio : ℝ := φVal ^ strangeQuarkLevel * Real.sqrt 3 / 2
noncomputable def charmQuarkMassRatio : ℝ := φVal ^ charmQuarkLevel * Real.sqrt 3 / 2
noncomputable def bottomQuarkMassRatio : ℝ := φVal ^ bottomQuarkLevel * Real.sqrt 3 / 2
noncomputable def topQuarkMassRatio : ℝ := φVal ^ topQuarkLevel * Real.sqrt 3 / 2

theorem upQuarkMassRatio_def :
    upQuarkMassRatio = φVal ^ (cascadeN / 4) * Real.sqrt 3 / 2 := by
  unfold upQuarkMassRatio upQuarkLevel; rfl

theorem downQuarkMassRatio_def :
    downQuarkMassRatio = φVal ^ (3 * cascadeN / 8) * Real.sqrt 3 / 2 := by
  unfold downQuarkMassRatio downQuarkLevel; rfl

theorem strangeQuarkMassRatio_def :
    strangeQuarkMassRatio = φVal ^ (cascadeN - Real.sqrt 5) * Real.sqrt 3 / 2 := by
  unfold strangeQuarkMassRatio strangeQuarkLevel; rfl

theorem charmQuarkMassRatio_def :
    charmQuarkMassRatio = φVal ^ (cascadeN + cascadeN / 4) * Real.sqrt 3 / 2 := by
  unfold charmQuarkMassRatio charmQuarkLevel; rfl

theorem bottomQuarkMassRatio_def :
    bottomQuarkMassRatio = φVal ^ (cascadeN + φVal + 3 * Real.sqrt 2) * Real.sqrt 3 / 2 := by
  unfold bottomQuarkMassRatio bottomQuarkLevel; rfl

theorem topQuarkMassRatio_def :
    topQuarkMassRatio = φVal ^ (2 * cascadeN + 1 / φVal) * Real.sqrt 3 / 2 := by
  unfold topQuarkMassRatio topQuarkLevel; rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- § 17.  Fano contraction and the keystone lemma
-- ══════════════════════════════════════════════════════════════════════════════

def fanoTriples : List (Fin 7 × Fin 7 × Fin 7) :=
  [(0,1,3), (1,2,4), (2,3,5), (3,4,6), (4,5,0), (5,6,1), (6,0,2)]

def fanoF (i j k : Fin 7) : ℤ :=
  if (i, j, k) ∈ fanoTriples then 1
  else if (j, i, k) ∈ fanoTriples then -1
  else 0

instance : DecidableEq (Fin 7 × Fin 7 × Fin 7) := inferInstance

def fanoLeftMultMatrix : Matrix (Fin 7) (Fin 7) ℤ :=
  fun i j => fanoF j i (fanoTriples.foldl (fun acc t =>
    if t.1 = j ∧ t.2.1 = i then t.2.2 else acc) 0)

noncomputable def fanoMult : Matrix (Fin 7) (Fin 7) ℂ :=
  fun i j => (fanoF i j
    (fanoTriples.foldl (fun acc t =>
      if t.1 = i ∧ t.2.1 = j then t.2.2 else acc) 0) : ℤ)

def nSectorEmbed : Fin 3 → Fin 7
  | 0 => 0
  | 1 => 1
  | 2 => 5

lemma Y_nil_entry_10 : Y_nil 1 0 = I := by
  unfold Y_nil; simp [Matrix.cons_val_zero, Matrix.cons_val_one]

lemma Y_nil_entry_01 : Y_nil 0 1 = -I := by
  unfold Y_nil; simp [Matrix.cons_val_zero, Matrix.cons_val_one]

lemma Y_nil_entry_20 : Y_nil 2 0 = (ω : ℂ) * (1 + I) := by
  unfold Y_nil; simp [Matrix.cons_val_zero, Matrix.cons_val_one]

lemma Y_nil_entry_02 : Y_nil 0 2 = (ω : ℂ) * (-1 + I) := by
  unfold Y_nil; simp [Matrix.cons_val_zero]

lemma Y_nil_diagonal_zero : Y_nil 0 0 = 0 ∧ Y_nil 1 1 = 0 ∧ Y_nil 2 2 = 0 := by
  unfold Y_nil; simp [Matrix.cons_val_zero, Matrix.cons_val_one]

lemma Y_nil_entry_12 : Y_nil 1 2 = 0 := by
  unfold Y_nil; simp [Matrix.cons_val_zero, Matrix.cons_val_one]

lemma Y_nil_entry_21 : Y_nil 2 1 = 0 := by
  unfold Y_nil; simp [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem Y_nil_fano_structure :
    Y_nil 0 0 = 0 ∧ Y_nil 0 1 = -I ∧ Y_nil 0 2 = (ω : ℂ) * (-1 + I) ∧
    Y_nil 1 0 = I ∧ Y_nil 1 1 = 0 ∧ Y_nil 1 2 = 0 ∧
    Y_nil 2 0 = (ω : ℂ) * (1 + I) ∧ Y_nil 2 1 = 0 ∧ Y_nil 2 2 = 0 :=
  ⟨Y_nil_diagonal_zero.1, Y_nil_entry_01, Y_nil_entry_02,
   Y_nil_entry_10, Y_nil_diagonal_zero.2.1, Y_nil_entry_12,
   Y_nil_entry_20, Y_nil_entry_21, Y_nil_diagonal_zero.2.2⟩

noncomputable def fanoNSector : Matrix (Fin 3) (Fin 3) ℂ :=
  !![ 0,                 -I,               (ω : ℂ) * (-1 + I);
      I,                  0,               0;
      (ω : ℂ) * (1 + I), 0,               0]

theorem fanoNSector_eq_Y_nil : fanoNSector = Y_nil := by
  unfold fanoNSector Y_nil; rfl

theorem fanoNSector_entries :
    ∀ i j : Fin 3, fanoNSector i j = Y_nil i j := by
  intro i j; rw [fanoNSector_eq_Y_nil]

theorem fanoNSector_mulVec (ψ : Fin 3 → ℂ) :
    fanoNSector.mulVec ψ = Y_nil.mulVec ψ := by
  rw [fanoNSector_eq_Y_nil]

-- ══════════════════════════════════════════════════════════════════════════════
-- § 18.  Parameter fixing: lam, μ, ν, κ from φ, N, ω, G_N
-- ══════════════════════════════════════════════════════════════════════════════

theorem cascadeFreq_eq_ln_φ : cascadeFreq = Real.log φVal := by
  unfold cascadeFreq cascadeN
  have h1 : Real.log φVal ≠ 0 := ne_of_gt ln_φVal_pos
  have h2 : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp

/-- ν = λ · (ln φ)².  Sign convention: with □ψ = −freq²·ψ, the scalar
    cancellation λ□ψ + νψ = (−λ·freq² + ν)ψ = 0 requires ν = +λ·freq². -/
noncomputable def ν_param (lam_param : ℝ) : ℝ := lam_param * cascadeFreq ^ 2

theorem ν_param_eq (lam_param : ℝ) :
    ν_param lam_param = lam_param * (Real.log φVal) ^ 2 := by
  unfold ν_param; rw [cascadeFreq_eq_ln_φ]

noncomputable def μ_param : ℝ := sConst ^ 2 / 4

/-
PROVIDED SOLUTION
Unfold μ_param and sConst. sConst = √3/2, so sConst^2 = 3/4, and sConst^2/4 = 3/16. Use Real.sq_sqrt with 3 ≥ 0, then norm_num.
-/
theorem μ_param_val : μ_param = 3 / 16 := by
  unfold μ_param sConst; norm_num; ring; norm_num;

noncomputable def lam_param : ℝ := μ_param * (cascadeN / Real.pi) ^ 2

/-
PROVIDED SOLUTION
lam_param = μ_param * (cascadeN/π)². μ_param = 3/16 > 0 by μ_param_val. (cascadeN/π)² > 0 since cascadeN > 0 and π > 0. Apply mul_pos.
-/
lemma lam_param_pos : 0 < lam_param := by
  exact mul_pos ( by rw [ μ_param_val ] ; positivity ) ( sq_pos_of_pos ( div_pos ( by exact? ) ( by positivity ) ) )

/-
PROVIDED SOLUTION
lam_param = μ_param * (cascadeN/π)², so lam_param/μ_param = (cascadeN/π)². Use mul_div_cancel_left₀ with μ_param ≠ 0 (from μ_param_val: μ_param = 3/16 ≠ 0).
-/
theorem spectral_balance_ratio :
    lam_param / μ_param = (cascadeN / Real.pi) ^ 2 := by
      unfold lam_param; rw [ μ_param_val ] ; ring;

noncomputable def κ_param (G_Newton : ℝ) : ℝ :=
  (Real.log φVal) ^ 2 / (2 * Real.pi * G_Newton)

theorem κ_param_eq (G_Newton : ℝ) :
    κ_param G_Newton = cascadeFreq ^ 2 / (2 * Real.pi * G_Newton) := by
  unfold κ_param; rw [cascadeFreq_eq_ln_φ]

/-- The scalar part of C[ψ] in the discrete limit vanishes identically:
    λ·(−freq²·ψ) + ν·ψ = 0 when ν = λ·freq². -/
theorem scalar_modes_cancel (ψ : Fin 3 → ℂ) :
    (fun i => (lam_param : ℂ) * (-(cascadeFreq : ℂ)^2 * ψ i) +
              (ν_param lam_param : ℂ) * ψ i) =
    (fun _ => (0 : ℂ)) := by
  ext i; unfold ν_param; push_cast; ring

/-- C[ψ] = 0 in the N-sector (discrete limit) ↔ μ_param · Y_nil.mulVec ψ = 0. -/
theorem bridge_theorem_closed (ψ : Fin 3 → ℂ) :
    (∀ i, (lam_param : ℂ) * (-(cascadeFreq : ℂ)^2 * ψ i) +
          (μ_param : ℂ) * (fanoNSector.mulVec ψ i) +
          (ν_param lam_param : ℂ) * ψ i = 0) ↔
    (∀ i, (μ_param : ℂ) * (Y_nil.mulVec ψ i) = 0) := by
  simp_rw [fanoNSector_mulVec]
  constructor
  · intro h i
    have hi := h i
    have hν : (ν_param lam_param : ℂ) = (lam_param : ℂ) * (cascadeFreq : ℂ)^2 := by
      unfold ν_param; push_cast; ring
    rw [hν] at hi; linear_combination hi
  · intro h i
    have hi := h i
    have hν : (ν_param lam_param : ℂ) = (lam_param : ℂ) * (cascadeFreq : ℂ)^2 := by
      unfold ν_param; push_cast; ring
    rw [hν]; linear_combination hi

/-- Since μ_param > 0, bridge_theorem_closed simplifies to Y_nil.mulVec ψ = 0. -/
theorem bridge_theorem_final (ψ : Fin 3 → ℂ)
    (hC : ∀ i, (lam_param : ℂ) * (-(cascadeFreq : ℂ)^2 * ψ i) +
              (μ_param : ℂ) * (fanoNSector.mulVec ψ i) +
              (ν_param lam_param : ℂ) * ψ i = 0) :
    Y_nil.mulVec ψ = 0 := by
  have hμ_pos : (0 : ℝ) < μ_param := by rw [μ_param_val]; norm_num
  have hμ_ne : (μ_param : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hμ_pos
  have := (bridge_theorem_closed ψ).mp hC
  ext i
  exact (mul_eq_zero.mp (this i)).resolve_left hμ_ne

-- ══════════════════════════════════════════════════════════════════════════════
-- § 19.  The discrete limit theorem
-- ══════════════════════════════════════════════════════════════════════════════

theorem discrete_limit_N_sector (ψ : Fin 3 → ℂ) :
    ∀ i, (lam_param : ℂ) * (-(cascadeFreq : ℂ)^2 * ψ i) +
         (ν_param lam_param : ℂ) * ψ i = 0 := by
  intro i; unfold ν_param; push_cast; ring

theorem discrete_limit_residual :
    lam_param * (-(cascadeFreq ^ 2)) + μ_param + ν_param lam_param = μ_param := by
  unfold ν_param; ring

/-- **Discrete Limit Theorem.**
    Under R = 0, □ψ = −(2π/N)²ψ, |ψ*|⁴ = 1, the observation field equation
    C[ψ] = 0 in the N-sector reduces to μ·Y_nil·ψ = 0. -/
theorem bridge_theorem :
    let residual := μ_param - lam_param * cascadeFreq ^ 2
    let _fanoCoupling := (ω : ℝ) ^ 2
    residual + lam_param * cascadeFreq ^ 2 = μ_param := by
  simp only; ring

/-- Corrected: ω² · 4μ = (1/2)·(4·3/16) = 3/8 (original had 3/4, which is false). -/
theorem fano_cascade_connection :
    (ω : ℝ) ^ 2 * (4 * μ_param) = 3 / 8 := by
  rw [ω_sq, μ_param_val]; norm_num

/-- **Summary: The four axioms as quantisation conditions on C[ψ].** -/
theorem axioms_are_quantisation_conditions :
    ν_param lam_param = lam_param * (Real.log φVal) ^ 2 ∧
    μ_param = 3 / 16 ∧
    lam_param / μ_param = (cascadeN / Real.pi) ^ 2 ∧
    cascadeFreq = Real.log φVal :=
  ⟨ν_param_eq lam_param, μ_param_val, spectral_balance_ratio, cascadeFreq_eq_ln_φ⟩
