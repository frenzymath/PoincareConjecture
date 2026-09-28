import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sard.EqualDimension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Germ.InverseFunction
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Perfect








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter IsManifold
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩



theorem exists_regular_value_sphere
    {f : S2 -> S2} (hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f)
    {U : Set S2} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ q ∈ U, ∀ x, f x = q -> Function.Bijective (mfderiv (𝓡 2) (𝓡 2) f x) := by
  obtain ⟨p, hp⟩ := hne
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num [E3]) (0 : E3)
      (by norm_num : (0 : Real) ≤ 1))
  let : Nontrivial S2 := ⟨⟨p, -p, ne_neg_of_mem_unit_sphere Real p⟩⟩
  have hUne : (U \ {f p}).Nonempty :=
    ((infinite_of_mem_nhds p (hU.mem_nhds hp)).sdiff (finite_singleton (f p))).nonempty
  let e := stereographic' 2 p
  have heatlas : e ∈ maximalAtlas (𝓡 2) ∞ S2 := by
    apply IsManifold.subset_maximalAtlas
    exact ⟨p, rfl⟩
  have hei : ContMDiff (𝓡 2) (𝓡 2) ∞ e.symm := by
    rw [← contMDiffOn_univ]
    simpa only [e, stereographic'_target] using
      contMDiffOn_symm_of_mem_maximalAtlas heatlas
  obtain ⟨q, hq, hreg⟩ := exists_regular_value_equal_dimension
    (hf.comp hei) (hU.sdiff isClosed_singleton) hUne
  refine ⟨q, hq.1, ?_⟩
  intro x hx
  have hxp : x ≠ p := by
    intro h
    exact hq.2 (by simpa only [mem_singleton_iff, h] using hx.symm)
  have hxe : x ∈ e.source := by simpa only [e, stereographic'_source, mem_compl_iff,
    mem_singleton_iff] using hxp
  have heq : e.symm (e x) = x := e.left_inv hxe
  have hc := hreg (e x) (by simpa only [Function.comp_apply, heq] using hx)
  have hchain := mfderiv_comp (e x)
    ((hf (e.symm (e x))).mdifferentiableAt (by simp))
    ((hei (e x)).mdifferentiableAt (by simp))
  rw [heq] at hchain
  have hsurj : Function.Surjective (mfderiv (𝓡 2) (𝓡 2) f x) := by
    intro v
    obtain ⟨w, hw⟩ := hc.surjective v
    refine ⟨mfderiv (𝓡 2) (𝓡 2) e.symm (e x) w, ?_⟩
    rw [hchain] at hw
    exact hw
  exact ⟨(LinearMap.injective_iff_surjective
    (V := EuclideanSpace Real (Fin 2))).mpr hsurj, hsurj⟩

theorem isOpen_regular_values_sphere
    {f : S2 -> S2} (hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f) :
    IsOpen {q | ∀ x, f x = q -> Function.Bijective (mfderiv (𝓡 2) (𝓡 2) f x)} := by
  have hiff (x : S2) : Function.Bijective (mfderiv (𝓡 2) (𝓡 2) f x) ↔
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x := by
    constructor
    · exact Poincare.isLocalDiffeomorphAt_of_contMDiffOn_bijective_mfderiv_modelSpace
        isOpen_univ hf.contMDiffOn (mem_univ x)
    · intro h
      exact (h.mfderivToContinuousLinearEquiv (by simp)).bijective
  have heq : {q | ∀ x, f x = q -> Function.Bijective (mfderiv (𝓡 2) (𝓡 2) f x)} =
      (f '' {x | ¬ IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x})ᶜ := by
    ext q
    simp only [mem_ofPred_eq, mem_compl_iff, mem_image, not_exists, not_and]
    constructor
    · intro h x hx he
      exact hx ((hiff x).mp (h x he))
    · intro h x hx
      apply (hiff x).mpr
      by_contra hn
      exact h x hn hx
  rw [heq]
  exact (((Poincare.isOpen_isLocalDiffeomorphAt (f := f)).isClosed_compl.isCompact).image
    hf.continuous).isClosed.isOpen_compl


theorem finite_fiber_of_regular_value_sphere
    {f : S2 -> S2} (hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f) {q : S2}
    (hq : ∀ x, f x = q -> Function.Bijective (mfderiv (𝓡 2) (𝓡 2) f x)) :
    (f ⁻¹' {q}).Finite := by
  have hcompact : IsCompact (f ⁻¹' {q}) :=
    (isClosed_singleton.preimage hf.continuous).isCompact
  apply hcompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hloc := Poincare.isLocalDiffeomorphAt_of_contMDiffOn_bijective_mfderiv_modelSpace
    isOpen_univ hf.contMDiffOn (mem_univ x) (hq x hx)
  obtain ⟨e, he, heq⟩ := hloc
  refine ⟨e.source, e.open_source, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hfy⟩
    apply mem_singleton_iff.mpr
    apply e.toPartialEquiv.injOn hy he
    exact (heq hy).symm.trans (hfy.trans (hx.symm.trans (heq he)))
  · rintro rfl
    exact ⟨he, hx⟩



theorem exists_antipodal_regular_values_sphere
    {f : S2 -> S2} (hf : ContMDiff (𝓡 2) (𝓡 2) ∞ f)
    {U : Set S2} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ q ∈ U,
      (∀ x, f x = q -> Function.Bijective (mfderiv (𝓡 2) (𝓡 2) f x)) ∧
      (∀ x, f x = -q -> Function.Bijective (mfderiv (𝓡 2) (𝓡 2) f x)) := by
  let R := {q | ∀ x, f x = q -> Function.Bijective (mfderiv (𝓡 2) (𝓡 2) f x)}
  have hRo : IsOpen R := isOpen_regular_values_sphere hf
  have hRd : Dense R := by
    apply dense_iff_inter_open.mpr
    intro V hV hVne
    obtain ⟨q, hqV, hq⟩ := exists_regular_value_sphere hf hV hVne
    exact ⟨q, hqV, hq⟩
  have hn : Continuous (fun q : S2 => -q) := by
    exact (continuous_subtype_val.neg).subtype_mk _
  have hnegU : ((fun q : S2 => -q) ⁻¹' U).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨-p, by simpa using hp⟩
  obtain ⟨p, hpU, hpR⟩ := hRd.inter_open_nonempty _ (hU.preimage hn) hnegU
  have hVne : (U ∩ (fun q : S2 => -q) ⁻¹' R).Nonempty :=
    ⟨-p, hpU, by simpa using hpR⟩
  obtain ⟨q, hq, hqR⟩ := hRd.inter_open_nonempty _ (hU.inter (hRo.preimage hn)) hVne
  exact ⟨q, hq.1, hqR, hq.2⟩

end Poincare.Manifold
