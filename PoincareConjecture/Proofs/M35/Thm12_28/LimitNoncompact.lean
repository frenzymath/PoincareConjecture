import PoincareConjecture.Proofs.M35.Thm12_28.BlowupSequence
import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem cylinder_source_noncompact {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J)
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) C a Q I U)
    (hU : U = univ) (s : ℝ) (hs : s ∈ I) (x₀ : C.carrier) :
    ¬ IsCompact (univ : Set C.carrier) := by
  subst U
  intro hcompact
  have htime : a + s / Q ∈ J := (e.forward s hs x₀).property
  let d := sliceDiffeomorph htime
  let f : C.carrier → StandardCapSpace := d ∘ e.forward s hs
  let g : StandardCapSpace → C.carrier := e.inverse s hs ∘ d.symm
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    d.contMDiff.comp (contMDiffOn_univ.mp (e.forward_smooth s hs))
  have hg : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (range f) := by
    apply (e.inverse_smooth s hs).comp d.symm.contMDiff.contMDiffOn
    rintro y ⟨z, rfl⟩
    exact ⟨z, mem_univ _, d.symm_apply_apply (e.forward s hs z)⟩
  have hleft : Function.LeftInverse g f := by
    intro z
    change e.inverse s hs (d.symm (d (e.forward s hs z))) = z
    exact (congrArg (e.inverse s hs) (d.symm_apply_apply (e.forward s hs z))).trans
      (e.left_inverse s hs (mem_univ z))
  have hcomp : g ∘ f = id := funext hleft
  have hbij (z : C.carrier) : Function.Bijective (mfderiv (𝓡 3) (𝓡 3) f z) := by
    have hd := mfderivWithin_comp z
      ((hg (f z) (mem_range_self z)).mdifferentiableWithinAt (by simp))
      ((hf.mdifferentiable (by simp) z).mdifferentiableWithinAt (s := univ))
      (fun y (_hy : y ∈ univ) => mem_range_self y)
      (uniqueMDiffWithinAt_univ (I := 𝓡 3) (x := z))
    rw [hcomp, mfderivWithin_univ, mfderivWithin_univ, mfderiv_id] at hd
    have hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) f z) := by
      apply Function.LeftInverse.injective (g := mfderivWithin (𝓡 3) (𝓡 3) g (range f) (f z))
      intro v
      exact (congrArg (fun L => L v) hd).symm
    let L : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (mfderiv (𝓡 3) (𝓡 3) f z).toLinearMap
    have hL : Function.Injective L := hinj
    have hsurj : Function.Surjective L := (LinearMap.injective_iff_surjective (f := L)).mp hL
    exact ⟨hinj, hsurj⟩
  have hopen : IsOpenMap f := isOpenMap_iff_nhds_le.mpr
    (fun z => (Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective (hf z) (hbij z)).ge)
  have hcompactRange : IsCompact (range f) := by
    simpa only [image_univ] using hcompact.image hf.continuous
  have hopenRange : IsOpen (range f) := by
    simpa only [image_univ] using hopen univ isOpen_univ
  have hclopen : IsClopen (range f) := ⟨hcompactRange.isClosed, hopenRange⟩
  have hrange : range f = univ := hclopen.eq_univ ⟨f x₀, mem_range_self x₀⟩
  exact noncompact_univ StandardCapSpace (hrange ▸ hcompactRange)

theorem blowupSequence_limit_noncompact (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    {J : Set ℝ} (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR) J) :
    ¬ IsCompact (univ : Set L.limit.sliceCarrier.carrier) := by
  intro hcompact
  obtain ⟨k, hk⟩ := hcompact.elim_directed_cover L.exhaustion.space
    L.exhaustion.space_open (by rw [L.exhaustion.space_covers])
    (fun i j => ⟨max i j, L.exhaustion.space_increasing (le_max_left _ _),
      L.exhaustion.space_increasing (le_max_right _ _)⟩)
  have hwhole : L.exhaustion.space k = univ := univ_subset_iff.mp hk
  exact cylinder_source_noncompact E.flow.base.flow (L.embedding k) hwhole 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ L.limit.base hcompact

end PoincareConjecture.M35.OrdinaryRealization
