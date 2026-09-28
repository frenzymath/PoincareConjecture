import PoincareConjecture.Proofs.M09.SmoothSquareAction

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_backwardPath_of_unitFamily {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (f : E × ℝ → M) (U : Set (E × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U)
    (v : E) (hsegment : ∀ r ∈ Set.Icc (0 : ℝ) 1, (v, r) ∈ U)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    ∃ P : BackwardTimePath F T 0 b,
      P.curve = (fun τ ↦ f (v, Real.sqrt τ / Real.sqrt b)) := by
  let α : ℝ → M := fun s ↦ f (v, s / Real.sqrt b)
  let D := (fun s : ℝ ↦ (v, s / Real.sqrt b)) ⁻¹' U
  have hi : ContDiff ℝ ∞ (fun s : ℝ ↦ (v, s / Real.sqrt b)) :=
    contDiff_const.prodMk (contDiff_id.div_const _)
  have hD : IsOpen D := hU.preimage hi.continuous
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D :=
    hf.comp hi.contMDiff.contMDiffOn (fun _ hs ↦ hs)
  have hpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hI : Set.Icc 0 (Real.sqrt b) ⊆ D := by
    intro s hs
    exact hsegment (s / Real.sqrt b)
      ⟨div_nonneg hs.1 hpos.le, (div_le_one hpos).mpr hs.2⟩
  obtain ⟨P, hP, _⟩ := exists_backwardPath_of_smoothSquareCurve F hM04 T τmax hτmax hwindow
    b hb hmax α D hD hI hα
  exact ⟨P, hP⟩

theorem contDiffOn_unitFamily_action {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (f : E × ℝ → M) (U : Set (E × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U)
    (V : Set E) (_hV : IsOpen V) (hVU : V ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U) :
    ContDiffOn ℝ ∞
      (fun z : E × ℝ ↦ backwardLLength F T 0 z.2
        (fun τ ↦ f (z.1, Real.sqrt τ / Real.sqrt z.2)))
      (V ×ˢ Set.Ioo 0 τmax) := by
  let S : Set ((E × ℝ) × ℝ) := (Set.univ ×ˢ Set.Ioo 0 τmax) ×ˢ Set.univ
  let Φ : (E × ℝ) × ℝ → E × ℝ := fun w ↦ (w.1.1, w.2 / Real.sqrt w.1.2)
  let D := S ∩ Φ ⁻¹' U
  let g : (E × ℝ) × ℝ → M := fun w ↦ f (Φ w)
  have hS : IsOpen S := (isOpen_univ.prod isOpen_Ioo).prod isOpen_univ
  have hroot : ContDiffOn ℝ ∞ (fun w : (E × ℝ) × ℝ ↦ Real.sqrt w.1.2) S :=
    contDiff_fst.snd.contDiffOn.sqrt (fun w hw ↦ hw.1.2.1.ne')
  have hΦ : ContDiffOn ℝ ∞ Φ S :=
    contDiff_fst.fst.contDiffOn.prodMk (contDiff_snd.contDiffOn.div hroot
      (fun w hw ↦ (Real.sqrt_pos.mpr hw.1.2.1).ne'))
  have hD : IsOpen D := hΦ.continuousOn.isOpen_inter_preimage hS hU
  have hg : ContMDiffOn (𝓘(ℝ, (E × ℝ) × ℝ)) (𝓡 n) ∞ g D :=
    hf.comp (hΦ.mono Set.inter_subset_left).contMDiffOn (fun w hw ↦ hw.2)
  intro z hz
  have hpos : 0 < Real.sqrt z.2 := Real.sqrt_pos.mpr hz.2.1
  have hsegment : ∀ r ∈ Set.Icc (0 : ℝ) 1, (z, Real.sqrt z.2 * r) ∈ D := by
    intro r hr
    refine ⟨⟨⟨Set.mem_univ _, hz.2⟩, Set.mem_univ _⟩, ?_⟩
    change (z.1, Real.sqrt z.2 * r / Real.sqrt z.2) ∈ U
    rw [mul_div_cancel_left₀ r hpos.ne']
    exact hVU ⟨hz.1, hr⟩
  have haction := contDiffAt_smoothSquareFamily_action F hM04 T τmax hτmax hwindow
    g D hD hg (z, z.2) hz.2 hsegment
  have hdiag : ContDiffAt ℝ ∞ (fun w : E × ℝ ↦ (w, w.2)) z :=
    contDiffAt_id.prodMk contDiffAt_snd
  exact (haction.comp z hdiag).contDiffWithinAt

end PoincareConjecture.Proofs.M09
