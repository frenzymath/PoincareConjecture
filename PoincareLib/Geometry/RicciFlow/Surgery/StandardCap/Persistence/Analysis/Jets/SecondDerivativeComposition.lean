import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Second derivative composition and smooth readouts

The twice-differentiated chain rule is proved in arbitrary normed
spaces before applying it to nested metric jets. This is the scalar
finite-jet calculation used in Morgan--Tian, equation (3.7), p. 41,
and Lemma 16.8, pp. 372-373; M44 derivation 26.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology BigOperators

namespace PoincareMT.M44

variable {E J F K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The actual second derivative of a composition, evaluated in two
directions. Only the smooth germs at the displayed points are used.
Source: the chain rule in the scalar finite-jet calculation, M44 derivation 26. -/
theorem second_fderiv_comp_of_contDiffAt {f : E → J} {g : J → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) (u v : E) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) x u v =
      fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) +
        fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x u v) := by
  have hf' := hf.fderiv_right (m := ∞) (by simp)
  have hg' := hg.fderiv_right (m := ∞) (by simp)
  have hchain := ((hg'.differentiableAt (by simp)).hasFDerivAt.comp x
    (hf.differentiableAt (by simp)).hasFDerivAt).clm_apply
      ((hf'.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have hcomp : ContDiffAt ℝ ∞ (g ∘ f) x := hg.comp x hf
  have heval := ((hcomp.fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have heq : (fun y => fderiv ℝ (g ∘ f) y v) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ g (f y) (fderiv ℝ f y v)) := by
    have hfe := (hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
    have hge := (hg.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
    filter_upwards [hfe, hf.continuousAt.eventually hge] with y hfy hgy
    rw [fderiv_comp y (hgy.differentiableAt (by simp)) (hfy.differentiableAt (by simp))]
    rfl
  have h := congrArg (fun A => A u)
    (heval.fderiv.symm.trans (heq.fderiv_eq.trans hchain.fderiv))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    Function.comp_apply, add_apply, zero_apply, map_zero, zero_add, add_zero, add_comm]
    using h

/-- The second chain-rule readout is smooth when its scalar function
and four input maps are smooth. Source: the scalar finite-jet
calculation in M44 derivation 26. -/
theorem contDiffAt_secondDerivative_readout {g : J → F} {a b c d : K → J} {x : K}
    (hg : ContDiffAt ℝ ∞ g (a x)) (ha : ContDiffAt ℝ ∞ a x)
    (hb : ContDiffAt ℝ ∞ b x) (hc : ContDiffAt ℝ ∞ c x) (hd : ContDiffAt ℝ ∞ d x) :
    ContDiffAt ℝ ∞ (fun y => fderiv ℝ (fderiv ℝ g) (a y) (b y) (c y) +
      fderiv ℝ g (a y) (d y)) x := by
  have hg' := hg.fderiv_right (m := ∞) (by simp)
  have hg'' := hg'.fderiv_right (m := ∞) (by simp)
  exact (((hg''.comp x ha).clm_apply hb).clm_apply hc).add ((hg'.comp x ha).clm_apply hd)

/-- The finite contraction of a second chain-rule jet, with its first
derivative correction, is smooth. The coefficient space is arbitrary;
in the scalar application it is the metric two-jet space. Source:
the coordinate Laplacian calculation in M44 derivation 26. -/
theorem contDiffAt_secondDerivativeJet_contraction {ι : Type*} [Fintype ι]
    {g : J → ℝ} (e : ι → E) {v : ι → J → E} {c : J → E}
    {x : J × (E →L[ℝ] J) × (E →L[ℝ] E →L[ℝ] J)}
    (hg : ContDiffAt ℝ ∞ g x.1)
    (hv : ∀ i, ContDiffAt ℝ ∞ (v i) x.1)
    (hc : ContDiffAt ℝ ∞ c x.1) :
    ContDiffAt ℝ ∞
      (fun y : J × (E →L[ℝ] J) × (E →L[ℝ] E →L[ℝ] J) =>
        (∑ i, (fderiv ℝ (fderiv ℝ g) y.1 (y.2.1 (e i)) (y.2.1 (v i y.1)) +
          fderiv ℝ g y.1 (y.2.2 (e i) (v i y.1)))) -
        fderiv ℝ g y.1 (y.2.1 (c y.1))) x := by
  have hA : ContDiffAt ℝ ∞
      (fun y : J × (E →L[ℝ] J) × (E →L[ℝ] E →L[ℝ] J) => y.2.1) x :=
    contDiffAt_snd.fst
  have hB : ContDiffAt ℝ ∞
      (fun y : J × (E →L[ℝ] J) × (E →L[ℝ] E →L[ℝ] J) => y.2.2) x :=
    contDiffAt_snd.snd
  apply ContDiffAt.sub
  · apply ContDiffAt.sum
    intro i _
    have hV := (hv i).comp x contDiffAt_fst
    exact contDiffAt_secondDerivative_readout hg contDiffAt_fst
      (hA.clm_apply contDiffAt_const) (hA.clm_apply hV)
      ((hB.clm_apply contDiffAt_const).clm_apply hV)
  · exact ((hg.fderiv_right (m := ∞) (by simp)).comp x contDiffAt_fst).clm_apply
      (hA.clm_apply (hc.comp x contDiffAt_fst))

/-- The scalar chain-rule contraction with arbitrary parameter maps.
The parameter space needs only a topology for its continuity theorem.
Source: the finite scalar contraction in M44 derivation 26. -/
noncomputable def secondDerivativeContractionReadout {X ι : Type*} [Fintype ι]
    (g : J → ℝ) (e : ι → E) (a : X → J) (b : X → E →L[ℝ] J)
    (d : X → E →L[ℝ] E →L[ℝ] J) (v : ι → X → E) (c : X → E) (x : X) : ℝ :=
  (∑ i, (fderiv ℝ (fderiv ℝ g) (a x) (b x (e i)) (b x (v i x)) +
    fderiv ℝ g (a x) (d x (e i) (v i x)))) - fderiv ℝ g (a x) (b x (c x))

/-- Continuity of the actual second chain-rule contraction uses only
continuous parameter maps. Source: equation (3.7), M44 derivation 26. -/
theorem continuousAt_secondDerivativeContractionReadout {X ι : Type*}
    [TopologicalSpace X] [Fintype ι]
    {g : J → ℝ} (e : ι → E) {a : X → J} {b : X → E →L[ℝ] J}
    {d : X → E →L[ℝ] E →L[ℝ] J} {v : ι → X → E} {c : X → E} {x : X}
    (hg : ContDiffAt ℝ ∞ g (a x)) (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hd : ContinuousAt d x) (hv : ∀ i, ContinuousAt (v i) x) (hc : ContinuousAt c x) :
    ContinuousAt (secondDerivativeContractionReadout g e a b d v c) x := by
  have hg' := hg.fderiv_right (m := ∞) (by simp)
  have hg'' := hg'.fderiv_right (m := ∞) (by simp)
  have hfirst := hg'.continuousAt.comp ha
  have hsecond := hg''.continuousAt.comp ha
  apply ContinuousAt.sub
  · apply tendsto_finsetSum
    intro i _
    exact ((hsecond.clm_apply (hb.clm_apply continuousAt_const)).clm_apply
      (hb.clm_apply (hv i))).add
        (hfirst.clm_apply ((hd.clm_apply continuousAt_const).clm_apply (hv i)))
  · exact hfirst.clm_apply (hb.clm_apply hc)

/-- The second chain-rule contraction, with its connection correction.
Keeping the jet space abstract shares the normed-space parameters in
the scalar application. Source: M44 derivation 26. -/
noncomputable def secondDerivativeJetContraction {ι : Type*} [Fintype ι]
    (g : J → ℝ) (e : ι → E) (v : ι → J → E) (c : J → E)
    (y : J × (E →L[ℝ] J) × (E →L[ℝ] E →L[ℝ] J)) : ℝ :=
  (∑ i, (fderiv ℝ (fderiv ℝ g) y.1 (y.2.1 (e i)) (y.2.1 (v i y.1)) +
    fderiv ℝ g y.1 (y.2.2 (e i) (v i y.1)))) -
    fderiv ℝ g y.1 (y.2.1 (c y.1))

/-- The scalar second-derivative contraction is continuous when its
coefficient maps are continuous. This is the regularity needed for
compact finite-jet bounds in M44 derivation 26. -/
theorem continuousAt_secondDerivativeJet_contraction {ι : Type*} [Fintype ι]
    {g : J → ℝ} (e : ι → E) {v : ι → J → E} {c : J → E}
    {x : J × (E →L[ℝ] J) × (E →L[ℝ] E →L[ℝ] J)}
    (hg : ContDiffAt ℝ ∞ g x.1)
    (hv : ∀ i, ContinuousAt (v i) x.1)
    (hc : ContinuousAt c x.1) :
    ContinuousAt (secondDerivativeJetContraction g e v c) x := by
  have hA : ContinuousAt
      (fun y : J × (E →L[ℝ] J) × (E →L[ℝ] E →L[ℝ] J) => y.2.1) x :=
    continuousAt_snd.fst
  have hB : ContinuousAt
      (fun y : J × (E →L[ℝ] J) × (E →L[ℝ] E →L[ℝ] J) => y.2.2) x :=
    continuousAt_snd.snd
  have hg' := hg.fderiv_right (m := ∞) (by simp)
  have hg'' := hg'.fderiv_right (m := ∞) (by simp)
  have hfirst := hg'.continuousAt.comp continuousAt_fst
  have hsecond := hg''.continuousAt.comp continuousAt_fst
  apply ContinuousAt.sub
  · apply tendsto_finsetSum
    intro i _
    have hV := (hv i).comp continuousAt_fst
    exact ((hsecond.clm_apply (hA.clm_apply continuousAt_const)).clm_apply
      (hA.clm_apply hV)).add
        (hfirst.clm_apply ((hB.clm_apply continuousAt_const).clm_apply hV))
  · exact hfirst.clm_apply (hA.clm_apply (hc.comp continuousAt_fst))

/-- A finite coordinate contraction of first and second chain-rule
derivatives. Only evaluations of the source jet are stored. Source:
the scalar Laplacian calculation in M44 derivation 26. -/
noncomputable def secondDerivativeArrayContraction {X ι : Type*} [Fintype ι]
    (g : J → ℝ) (a : X → J) (b : ι → X → J) (d : ι → ι → X → J)
    (v : ι → ι → X → ℝ) (c : ι → X → ℝ) (x : X) : ℝ :=
  (∑ i, ∑ j, v i j x * (fderiv ℝ (fderiv ℝ g) (a x) (b i x) (b j x) +
    fderiv ℝ g (a x) (d i j x))) - ∑ i, c i x * fderiv ℝ g (a x) (b i x)

/-- Continuity of the finite coordinate chain-rule contraction.
The parameter space needs only a topology. Source: the finite-jet
compactness estimate in M44 derivation 26. -/
theorem continuousAt_secondDerivativeArrayContraction {X ι : Type*}
    [TopologicalSpace X] [Fintype ι]
    {g : J → ℝ} {a : X → J} {b : ι → X → J} {d : ι → ι → X → J}
    {v : ι → ι → X → ℝ} {c : ι → X → ℝ} {x : X}
    (hg : ContDiffAt ℝ ∞ g (a x)) (ha : ContinuousAt a x)
    (hb : ∀ i, ContinuousAt (b i) x) (hd : ∀ i j, ContinuousAt (d i j) x)
    (hv : ∀ i j, ContinuousAt (v i j) x) (hc : ∀ i, ContinuousAt (c i) x) :
    ContinuousAt (secondDerivativeArrayContraction g a b d v c) x := by
  have hg' := hg.fderiv_right (m := ∞) (by simp)
  have hg'' := hg'.fderiv_right (m := ∞) (by simp)
  have hfirst := hg'.continuousAt.comp ha
  have hsecond := hg''.continuousAt.comp ha
  apply ContinuousAt.sub
  · apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (hv i j).mul (((hsecond.clm_apply (hb i)).clm_apply (hb j)).add
      (hfirst.clm_apply (hd i j)))
  · apply tendsto_finsetSum
    intro i _
    exact (hc i).mul (hfirst.clm_apply (hb i))

/-- Evaluation on vectors of norm at most one preserves a common
bound on the value and its first two derivative slots. Source:
the finite coordinate package in M44 derivation 26. -/
theorem norm_coordinateDerivativeArray_le {ι : Type*} [Fintype ι]
    (e : ι → E) (he : ∀ i, ‖e i‖ ≤ 1) (z : J)
    (A : E →L[ℝ] J) (B : E →L[ℝ] E →L[ℝ] J) {C : ℝ}
    (hz : ‖z‖ ≤ C) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) :
    ‖(z, (fun i => A (e i)), (fun i j => B (e i) (e j)))‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg z).trans hz
  have hfirst (i : ι) : ‖A (e i)‖ ≤ C :=
    (A.le_opNorm (e i)).trans ((mul_le_mul hA (he i) (norm_nonneg _) hC).trans_eq (mul_one C))
  have hsec (i j : ι) : ‖B (e i) (e j)‖ ≤ C := by
    have hi : ‖B (e i)‖ ≤ C :=
      (B.le_opNorm (e i)).trans
        ((mul_le_mul hB (he i) (norm_nonneg _) hC).trans_eq (mul_one C))
    exact ((B (e i)).le_opNorm (e j)).trans
      ((mul_le_mul hi (he j) (norm_nonneg _) hC).trans_eq (mul_one C))
  exact max_le hz (max_le ((pi_norm_le_iff_of_nonneg hC).mpr hfirst)
    ((pi_norm_le_iff_of_nonneg hC).mpr fun i => (pi_norm_le_iff_of_nonneg hC).mpr (hsec i)))

end PoincareMT.M44
