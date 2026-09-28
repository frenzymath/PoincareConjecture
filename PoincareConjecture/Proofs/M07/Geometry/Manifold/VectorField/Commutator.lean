import PoincareConjecture.Proofs.M07.Geometry.Manifold.VectorField.Derivation











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set Filter

namespace Poincare.Manifold.VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]



theorem mfderiv_mlieBracket_eq_commutator_of_contMDiffAt
    (X Y : (x : M) → TangentSpace I x)
    {f : M → ℝ} (p : M) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f p)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) p)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) p) :
    mvfderiv I f p (VectorField.mlieBracket I X Y p) =
      mvfderiv I (fun q ↦ mvfderiv I f q (Y q)) p (X p) -
        mvfderiv I (fun q ↦ mvfderiv I f q (X q)) p (Y p) := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hpe : (extChartAt I p).symm (extChartAt I p p) = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source p)
  have hmem : extChartAt I p p ∈ (extChartAt I p).target := mem_extChartAt_target p
  have htopen : IsOpen (extChartAt I p).target := isOpen_extChartAt_target p
  let g : E → ℝ := f ∘ (extChartAt I p).symm
  let V : E → E := VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm X
  let W : E → E := VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Y
  have hfmdiff : ∀ᶠ q in 𝓝 p, MDifferentiableAt I 𝓘(ℝ, ℝ) f q := by
    have hfinite : ContMDiffAt I 𝓘(ℝ, ℝ) 1 f p := hf.of_le (by simp)
    exact ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hfinite).mono
      fun q hq ↦ hq.mdifferentiableAt one_ne_zero
  have hgC : ContDiffAt ℝ ∞ g (extChartAt I p p) := by
    have hsymm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm
        (Set.range I) (extChartAt I p p) := contMDiffWithinAt_extChartAt_symm_range p hmem
    have hcd : ContDiffWithinAt ℝ ∞ (f ∘ (extChartAt I p).symm)
        (Set.range I) (extChartAt I p p) :=
      (hf.comp_contMDiffWithinAt_of_eq hsymm hpe).contDiffWithinAt
    rwa [I.range_eq_univ, contDiffWithinAt_univ] at hcd
  have hdiff (Z : (x : M) → TangentSpace I x)
      (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun x ↦ (⟨x, Z x⟩ : TangentBundle I M)) p) :
      DifferentiableAt ℝ
        (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z) (extChartAt I p p) := by
    have h := hZ.mdifferentiableWithinAt (s := Set.univ)
      |>.differentiableWithinAt_mpullbackWithin_vectorField
    rw [Set.preimage_univ, Set.univ_inter, I.range_eq_univ, differentiableWithinAt_univ,
      VectorField.mpullbackWithin_univ] at h
    exact h
  have hLHS : mfderiv I 𝓘(ℝ, ℝ) f p (VectorField.mlieBracket I X Y p) =
      fderiv ℝ g (extChartAt I p p) (VectorField.lieBracket ℝ V W (extChartAt I p p)) := by
    have hact := mfderiv_action_eq_fderiv_pullback (h := f) (p := p) (z := extChartAt I p p)
      hmem (by rw [hpe]; exact hfmdiff.self_of_nhds) (VectorField.mlieBracket I X Y)
    rw [hpe] at hact
    rw [← hact]
    congr 1
    rw [VectorField.mpullback_mlieBracket
        (hpe.symm ▸ hX) (hpe.symm ▸ hY)
        ((contMDiffOn_extChartAt_symm p).contMDiffAt (htopen.mem_nhds hmem)) le_rfl,
      ← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin_univ]
  have hEA (Z : (x : M) → TangentSpace I x) :
      (fun q ↦ mfderiv I 𝓘(ℝ, ℝ) f q (Z q)) ∘ (extChartAt I p).symm
        =ᶠ[𝓝 (extChartAt I p p)]
      (fun z ↦ fderiv ℝ g z
        (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z z)) := by
    have hsymm := ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      (htopen.mem_nhds hmem)).continuousAt
    rw [ContinuousAt, hpe] at hsymm
    filter_upwards [htopen.mem_nhds hmem, hsymm.eventually hfmdiff] with z hz hzf
    exact (mfderiv_action_eq_fderiv_pullback hz hzf Z).symm
  have hterm (Z₁ Z₂ : (x : M) → TangentSpace I x)
      (hZ₂ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun x ↦ (⟨x, Z₂ x⟩ : TangentBundle I M)) p) :
      mfderiv I 𝓘(ℝ, ℝ) (fun q ↦ mfderiv I 𝓘(ℝ, ℝ) f q (Z₂ q)) p (Z₁ p) =
        fderiv ℝ (fun z ↦ fderiv ℝ g z
          (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z₂ z))
          (extChartAt I p p)
          (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z₁ (extChartAt I p p)) := by
    have hrhs_diff : DifferentiableAt ℝ
        (fun z ↦ fderiv ℝ g z
          (VectorField.mpullback 𝓘(ℝ, E) I (extChartAt I p).symm Z₂ z))
        (extChartAt I p p) := by
      have hfd : DifferentiableAt ℝ (fun z ↦ fderiv ℝ g z) (extChartAt I p p) :=
        (hgC.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
      exact hfd.clm_apply (hdiff Z₂ hZ₂)
    have hZ₂f_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun q ↦ mfderiv I 𝓘(ℝ, ℝ) f q (Z₂ q)) p := by
      have hcomp_diff : DifferentiableAt ℝ
          ((fun q ↦ mfderiv I 𝓘(ℝ, ℝ) f q (Z₂ q)) ∘ (extChartAt I p).symm)
          (extChartAt I p p) := hrhs_diff.congr_of_eventuallyEq (hEA Z₂)
      have hcomp_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
          ((fun q ↦ mfderiv I 𝓘(ℝ, ℝ) f q (Z₂ q)) ∘ (extChartAt I p).symm)
          (extChartAt I p p) := hcomp_diff.mdifferentiableAt
      have hchart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) p :=
        mdifferentiableAt_extChartAt (mem_chart_source H p)
      have hcong : ((fun q ↦ mfderiv I 𝓘(ℝ, ℝ) f q (Z₂ q)) ∘ (extChartAt I p).symm)
          ∘ (extChartAt I p) =ᶠ[𝓝 p] (fun q ↦ mfderiv I 𝓘(ℝ, ℝ) f q (Z₂ q)) := by
        filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds (mem_extChartAt_source p)]
          with q hq
        show mfderiv I 𝓘(ℝ, ℝ) f ((extChartAt I p).symm (extChartAt I p q))
            (Z₂ ((extChartAt I p).symm (extChartAt I p q))) =
          mfderiv I 𝓘(ℝ, ℝ) f q (Z₂ q)
        rw [(extChartAt I p).left_inv hq]
      exact (hcomp_mdiff.comp p hchart).congr_of_eventuallyEq hcong.symm
    have hact := mfderiv_action_eq_fderiv_pullback
      (h := fun q ↦ mfderiv I 𝓘(ℝ, ℝ) f q (Z₂ q))
      (p := p) (z := extChartAt I p p) hmem (by rw [hpe]; exact hZ₂f_mdiff) Z₁
    rw [hpe] at hact
    rw [← hact, (hEA Z₂).fderiv_eq]
  change (mfderiv I 𝓘(ℝ, ℝ) f p (VectorField.mlieBracket I X Y p) : ℝ) =
    @Sub.sub ℝ _
      (mfderiv I 𝓘(ℝ, ℝ) (fun q ↦ (mfderiv I 𝓘(ℝ, ℝ) f q (Y q) : ℝ)) p (X p))
      (mfderiv I 𝓘(ℝ, ℝ) (fun q ↦ (mfderiv I 𝓘(ℝ, ℝ) f q (X q) : ℝ)) p (Y p))
  rw [hLHS, hterm X Y hY, hterm Y X hX]
  exact VectorField.fderiv_apply_lieBracket (n := ∞) hgC
    (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
    (hdiff Y hY) (hdiff X hX)



theorem mfderiv_mlieBracket_eq_commutator
    (X Y : (x : M) → TangentSpace I x)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M)
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) p)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) p) :
    mvfderiv I f p (VectorField.mlieBracket I X Y p) =
      mvfderiv I (fun q ↦ mvfderiv I f q (Y q)) p (X p) -
        mvfderiv I (fun q ↦ mvfderiv I f q (X q)) p (Y p) :=
  mfderiv_mlieBracket_eq_commutator_of_contMDiffAt X Y p (hf p) hX hY

end Poincare.Manifold.VectorField
