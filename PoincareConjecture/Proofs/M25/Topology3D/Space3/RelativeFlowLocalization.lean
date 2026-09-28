import PoincareConjecture.Proofs.M25.Topology3D.Space3.BackwardTrackLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.InwardFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow












set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_relative_ball_compression (f : E → E)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {k l : ℝ≥0} (hk : LipschitzWith k f) (hl : ∀ x, ‖f x‖ ≤ l)
    (hinward : ∀ x, ‖x‖ = 1 → ⟪x, f x⟫_ℝ ≤ 0)
    {D V Ω : Set E} (hD : IsClosed D) (hV : IsOpen V) (hDV : D ⊆ V)
    (hΩ : IsOpen Ω) (hBΩ : closedBall (0 : E) 1 \ D ⊆ Ω)
    {T : ℝ} (hT : 0 ≤ T)
    (hpres : ∀ t ∈ Icc 0 T, MapsTo (fun x => boundedFlow f hk hl x t) D D)
    (hfinal : MapsTo (fun x => boundedFlow f hk hl x T) (closedBall 0 1) V) :
    ∃ Ψ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Ψ p.1 p.2) ∧
      (∀ x, Ψ 0 x = x) ∧
      (∀ t : ℝ, 0 ≤ t → MapsTo (Ψ t) (closedBall 0 1) (closedBall 0 1)) ∧
      MapsTo (Ψ T) (closedBall 0 1) V ∧
      (∀ t x, x ∈ D → Ψ t x = x) ∧
      ∃ C : Set E, IsCompact C ∧ C ⊆ Ω \ D ∧ ∀ t x, x ∉ C → Ψ t x = x := by
  let K : Set E := closedBall 0 1 \ V
  let C : Set E :=
    (fun p : ℝ × E => boundedFlow f hk hl p.2 (-p.1)) '' (Icc 0 T ×ˢ K) ∩ closedBall 0 1
  have hK : IsCompact K := (isCompact_closedBall (0 : E) 1).diff hV
  have htrack : Continuous (fun p : ℝ × E => boundedFlow f hk hl p.2 (-p.1)) :=
    (boundedFlow_contDiff f hk hl hf hfc).continuous.comp
      (continuous_snd.prodMk continuous_fst.neg)
  have hC : IsCompact C :=
    ((isCompact_Icc.prod hK).image htrack).inter_right isClosed_closedBall
  have hCD : C ⊆ Ω \ D := by
    rintro x ⟨⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩, hx⟩
    have hnot : boundedFlow f hk hl y (-t) ∉ D := by
      intro hxD
      have hh := hDV (hpres t ht hxD)
      change boundedFlow f hk hl (boundedFlow f hk hl y (-t)) t ∈ V at hh
      rw [← boundedFlow_add, neg_add_cancel, boundedFlow_zero] at hh
      exact hy.2 hh
    exact ⟨hBΩ ⟨hx, hnot⟩, hnot⟩
  obtain ⟨ρ, hρ, hρc, hρs, hρnear, hρrange⟩ :=
    exists_compact_smooth_cutoff hC (hΩ.inter hD.isOpen_compl) hCD
  let g : E → E := fun x => ρ x • f x
  have hg : ContDiff ℝ ∞ g := hρ.smul hf
  have hgc : HasCompactSupport g := hρc.smul_right
  have hgs : tsupport g ⊆ Ω \ D := (tsupport_smul_subset_left ρ f).trans hρs
  obtain ⟨kg, lg, hgK, hgL⟩ := compactField_bounds g hg hgc
  have hginward (x : E) (hx : ‖x‖ = 1) : ⟪x, g x⟫_ℝ ≤ 0 := by
    change ⟪x, ρ x • f x⟫_ℝ ≤ 0
    rw [real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos (hρrange x).1 (hinward x hx)
  have hball (t : ℝ) (ht : 0 ≤ t) :
      MapsTo (fun x => boundedFlow g hgK hgL x t) (closedBall 0 1) (closedBall 0 1) :=
    boundedFlow_mapsTo_closedBall g hgK hgL hginward t ht
  have hgend : MapsTo (fun x => boundedFlow g hgK hgL x T) (closedBall 0 1) V := by
    apply boundedFlow_mapsTo_of_backward_agreement f g hk hl hgK hgL hT
      (fun t ht => hball t ht.1) hfinal
    intro t ht y hy hx
    have hxC : boundedFlow f hk hl y (-t) ∈ C :=
      ⟨⟨(t, y), ⟨ht, hy⟩, rfl⟩, hx⟩
    filter_upwards [eventually_nhdsSet_iff_forall.mp hρnear _ hxC] with z hz
    change ρ z • f z = f z
    rw [hz, one_smul]
  let Ψ := fun t => boundedFlowDiffeomorph g hgK hgL hg hgc t
  refine ⟨Ψ, ?_, ?_, hball, hgend, ?_, tsupport g, hgc.isCompact, hgs, ?_⟩
  · exact (boundedFlow_contDiff g hgK hgL hg hgc).comp
      (contDiff_snd.prodMk contDiff_fst)
  · intro x
    exact boundedFlow_zero g hgK hgL x
  · intro t x hx
    apply boundedFlow_eq_self g hgK hgL x
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs => (hgs hs).2 hx
  · intro t x hx
    exact boundedFlow_eq_self g hgK hgL x (image_eq_zero_of_notMem_tsupport hx) t

end PoincareConjecture.M25.Topology3D
