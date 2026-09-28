import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.CollarInteriorPush
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.OneSidedCollarRestriction
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.PathMaps









set_option autoImplicit false
open Set

namespace Poincare.Topology

theorem exists_loop_off_collar_rim
    {E X : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X) (hc : ContinuousOn c (K ×ˢ Icc (0 : ℝ) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ico (0 : ℝ) r)))
    (x : ↥((c '' (K ×ˢ ({0} : Set ℝ)))ᶜ))
    (hx : (x : X) ∉ c '' (K ×ˢ Ico (0 : ℝ) (r / 2)))
    (gamma : Path (x : X) x) :
    ∃ eta : Path x x, gamma.Homotopic (eta.map continuous_subtype_val) := by
  obtain ⟨D, hzero, _, hfixed, hend, _⟩ := exists_collar_interior_push hK hr c hc hi ho
  let eta : Path x x := {
    toFun := fun t => ⟨D (1, gamma t), hend (gamma t)⟩
    continuous_toFun := (D.continuous.comp (continuous_const.prodMk gamma.continuous)).subtype_mk _
    source' := Subtype.ext (by change D (1, gamma 0) = x; rw [gamma.source, hfixed 1 x hx])
    target' := Subtype.ext (by change D (1, gamma 1) = x; rw [gamma.target, hfixed 1 x hx]) }
  refine ⟨eta, ⟨{
    toFun := fun z => D (z.1, gamma z.2)
    continuous_toFun := D.continuous.comp (continuous_fst.prodMk (gamma.continuous.comp continuous_snd))
    map_zero_left := fun t => hzero (gamma t)
    map_one_left := fun _ => rfl
    prop' := ?_ }⟩⟩
  intro t s hs
  rcases hs with hs | hs
  · subst s
    change D (t, gamma 0) = gamma 0
    rw [gamma.source, hfixed t x hx]
  · subst s
    change D (t, gamma 1) = gamma 1
    rw [gamma.target, hfixed t x hx]

theorem fundamentalGroup_collar_rim_complement_surjective_of_fixed
    {E X : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X) (hc : ContinuousOn c (K ×ˢ Icc (0 : ℝ) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ico (0 : ℝ) r)))
    (x : ↥((c '' (K ×ˢ ({0} : Set ℝ)))ᶜ))
    (hx : (x : X) ∉ c '' (K ×ˢ Ico (0 : ℝ) (r / 2))) :
    Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥((c '' (K ×ˢ ({0} : Set ℝ)))ᶜ), X)) x) := by
  intro gamma
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective gamma
  obtain ⟨q, hq⟩ := exists_loop_off_collar_rim hK hr c hc hi ho x hx p
  exact ⟨Path.Homotopic.Quotient.mk q, Path.Homotopic.Quotient.eq.mpr hq.symm⟩

theorem fundamentalGroup_collar_rim_complement_surjective
    {E X : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X) (hc : ContinuousOn c (K ×ˢ Icc (0 : ℝ) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (0 : ℝ) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ico (0 : ℝ) r)))
    (x : ↥((c '' (K ×ˢ ({0} : Set ℝ)))ᶜ)) :
    Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥((c '' (K ×ˢ ({0} : Set ℝ)))ᶜ), X)) x) := by
  obtain ⟨delta, hd, hdr, havoid⟩ := exists_oneSided_collar_width_avoiding_point hr c hi x.property
  have hsub : K ×ˢ Icc (0 : ℝ) delta ⊆ K ×ˢ Icc (0 : ℝ) r :=
    prod_mono Subset.rfl (Icc_subset_Icc_right hdr)
  have hi' : Topology.IsEmbedding (fun z : (K ×ˢ Icc (0 : ℝ) delta : Set (E × ℝ)) => c z) :=
    hi.comp (Topology.IsEmbedding.inclusion hsub)
  apply fundamentalGroup_collar_rim_complement_surjective_of_fixed hK hd c (hc.mono hsub) hi'
    (isOpen_smaller_oneSided_collar hdr c hi ho) x
  intro hx
  apply havoid
  apply image_mono (prod_mono Subset.rfl ?_) hx
  intro t ht
  exact ⟨ht.1, by linarith [ht.2]⟩

end Poincare.Topology
