import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.LocalPLInvariance
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainMaps
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasNeighborhood
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

set_option backward.isDefEq.respectTransparency false in
theorem ChartwisePLMap.isLocalHomeomorph_of_open
    {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3}
    {d : κ → OpenPartialHomeomorph Y V3} {R : Set X} {T : Set Y}
    {f : C(R, T)} (hf : ChartwisePLMap e d f)
    (hR : IsOpen R) (hT : IsOpen T) (hinj : IsLocallyInjective f) :
    IsLocalHomeomorph f := by
  classical
  intro x
  obtain ⟨W, hW, hxW, hinjW⟩ := hinj x
  obtain ⟨i, j, K, V, F, hK, hV, hxV, _, hVi, hVK, hKt, _, hF, hvalue⟩ :=
    hf.coordinates x (mem_univ _)
  let q : OpenPartialHomeomorph R V3 :=
    (e i).subtypeRestr (s := ⟨R, hR⟩) ⟨x⟩
  let q' : OpenPartialHomeomorph T V3 :=
    (d j).subtypeRestr (s := ⟨T, hT⟩) ⟨f x⟩
  have hqV : V ⊆ q.source := by
    intro y hy
    change y ∈ ((e i).subtypeRestr (s := ⟨R, hR⟩) ⟨x⟩).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact hVi hy
  have hformula (y : R) (hy : y ∈ V) :
      f y ∈ q'.source ∧ F (q y) = q' (f y) := by
    obtain ⟨hyj, hyF⟩ := hvalue y (hVi hy) (hVK ⟨y, hy, rfl⟩)
    constructor
    · change f y ∈ ((d j).subtypeRestr (s := ⟨T, hT⟩) ⟨f x⟩).source
      rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact hyj
    · exact hyF
  let U : Set V3 := q '' (V ∩ W)
  have hU : IsOpen U := q.isOpen_image_of_subset_source (hV.inter hW)
    (inter_subset_left.trans hqV)
  have hxU : q x ∈ U := ⟨x, ⟨hxV, hxW⟩, rfl⟩
  have hUt : U ⊆ q.target := by
    rintro z ⟨y, hy, rfl⟩
    exact q.map_source (hqV hy.1)
  have hUK : U ⊆ K.space := by
    rintro z ⟨y, hy, rfl⟩
    exact hVK ⟨y, hy.1, rfl⟩
  have hlocal : LocallyPiecewiseAffineOn F U :=
    hF.locallyPiecewiseAffineOn_of_subset_interior hU
      (hU.subset_interior_iff.mpr hUK)
  have hfinj : InjOn F U := by
    rintro z ⟨y, hy, rfl⟩ w ⟨v, hv, rfl⟩ heq
    have hfv : f y = f v := q'.injOn (hformula y hy.1).1 (hformula v hv.1).1
      ((hformula y hy.1).2.symm.trans (heq.trans (hformula v hv.1).2))
    exact congrArg q (hinjW hy.2 hv.2 hfv)
  have hcoord : LocallyPiecewiseAffineOn (q' ∘ f ∘ q.symm) U :=
    hlocal.congr (by
      rintro z ⟨y, hy, rfl⟩
      simp only [Function.comp_apply, q.left_inv (hqV hy.1)]
      exact (hformula y hy.1).2)
  have hcoordInj : InjOn (q' ∘ f ∘ q.symm) U := by
    intro z hz w hw heq
    apply hfinj hz hw
    have heqF : EqOn F (q' ∘ f ∘ q.symm) U := by
      rintro z ⟨y, hy, rfl⟩
      simp only [Function.comp_apply, q.left_inv (hqV hy.1)]
      exact (hformula y hy.1).2
    exact (heqF hz).trans (heq.trans (heqF hw).symm)
  have hLH := hcoord.isLocalHomeomorphOn_of_locallyInjective rfl (by
    intro z
    exact ⟨univ, isOpen_univ, mem_univ _, fun y _ v _ heq =>
      Subtype.ext (hcoordInj y.property v.property heq)⟩)
  have hsource (z : V3) (hz : z ∈ U) : f (q.symm z) ∈ q'.source := by
    obtain ⟨y, hy, rfl⟩ := hz
    rw [q.left_inv (hqV hy.1)]
    exact (hformula y hy.1).1
  have hfq : IsLocalHomeomorphOn (f ∘ q.symm) U :=
    hLH.of_comp_left
      ((IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn q').mono (by
        rintro _ ⟨z, hz, rfl⟩
        exact hsource z hz))
      (fun z hz => f.continuous.continuousAt.comp (q.symm.continuousAt (hUt hz)))
  have hresult := hfq.of_comp_right
    ((IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn q.symm).mono hUt)
  exact hresult x ⟨q x, hxU, q.left_inv (hqV hxV)⟩

end PoincareConjecture.M76
