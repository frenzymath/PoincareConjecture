import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardSphereLift
import PoincareConjecture.Proofs.M76.Mathlib.RelativePolyhedralNeighborhood
import Mathlib.Topology.Algebra.ContinuousAffineEquiv










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
  {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

local notation "V" => ((ι → ℝ) × (κ → ℝ))
local notation "W" => LatticeHandleAmbient ι κ L





theorem StandardLatticeHandleAtlas.finitePiecewiseAffineOn_lift
    {d : α → OpenPartialHomeomorph W (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas ι κ L d)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (f : E → W) (hf : PolyhedralPLInCharts d f K.space)
    (g : E → V) (hg : ContinuousOn g K.space)
    (hproj : ∀ x ∈ K.space, ((g x).1, QuotientAddGroup.mk (g x).2) = f x) :
    FinitePiecewiseAffineOn g K.space := by
  let p : V →+ W :=
    (AddMonoidHom.id (ι → ℝ)).prodMap (QuotientAddGroup.mk' L.toAddSubgroup)
  have hq : IsCoveringMap
      (QuotientAddGroup.mk : (κ → ℝ) → ((κ → ℝ) ⧸ L.toAddSubgroup)) :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap
  have hp : IsLocalHomeomorph p := hq.id_prod.isLocalHomeomorph
  have hfp : Continuous (fun x : K.space => f x) :=
    hf.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property)
  have hgp : Continuous (fun x : K.space => g x) :=
    hg.comp_continuous continuous_subtype_val (fun x => x.property)
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  obtain ⟨i, J, O, hJ, hJK, hO, hxO, hOJ, hfJ, hcoords⟩ := hf.coordinates x
  have hxJ : (x : E) ∈ J.space := hOJ (mem_image_of_mem Subtype.val hxO)
  have hfx : f x ∈ (d i).source := hfJ hxJ
  obtain ⟨a0, ha0⟩ := hd.inverse_formula i
  let z0 := d i (f x)
  have hz0 : z0 ∈ (d i).target := (d i).mapsTo hfx
  have hcenter : p (a0 z0) = f x :=
    (ha0 z0 hz0).symm.trans ((d i).left_inv hfx)
  let delta : V := g x - a0 z0
  have hdelta : p delta = 0 := by
    change p (g x - a0 z0) = 0
    rw [map_sub, show p (g x) = f x from hproj x x.property, hcenter, sub_self]
  let a := a0.trans (ContinuousAffineEquiv.constVAdd ℝ V delta)
  have haz : a z0 = g x := by
    change (g x - a0 z0) + a0 z0 = g x
    exact sub_add_cancel _ _
  have ha (z : Fin 3 → ℝ) (hz : z ∈ (d i).target) :
      p (a z) = (d i).symm z := by
    change p (delta + a0 z) = (d i).symm z
    rw [map_add, hdelta, zero_add]
    exact (ha0 z hz).symm
  obtain ⟨U, hU, hxU, hinj⟩ := hp.isLocallyInjective (g x)
  let T : Set W := (d i).source ∩ (d i) ⁻¹' (a ⁻¹' U)
  have hT : IsOpen T := (d i).isOpen_inter_preimage (hU.preimage a.continuous)
  let O' : Set K.space := O ∩ (fun y : K.space => g y) ⁻¹' U ∩
    (fun y : K.space => f y) ⁻¹' T
  have hO' : IsOpen O' := (hO.inter (hU.preimage hgp)).inter (hT.preimage hfp)
  have hxO' : x ∈ O' := by
    refine ⟨⟨hxO, hxU⟩, hfx, ?_⟩
    change a z0 ∈ U
    rwa [haz]
  obtain ⟨N, O'', hN, hNK, hO'', hxO'', hON, hNO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO' hxO'
  have hyO (y : E) (hy : y ∈ N.space) : (⟨y, hNK hy⟩ : K.space) ∈ O' := hNO hy
  have hNJ : N.space ⊆ J.space := by
    intro y hy
    exact hOJ (mem_image_of_mem Subtype.val (hyO y hy).1.1)
  have hlocal : FinitePiecewiseAffineOn g N.space := by
    apply ((hcoords.restrict N hN hNJ).postcomp a.toContinuousAffineMap).congr
    intro y hy
    have hys : f y ∈ (d i).source := (hyO y hy).2.1
    apply hinj (hyO y hy).2.2 (hyO y hy).1.2
    rw [ha _ ((d i).mapsTo hys), (d i).left_inv hys]
    exact (hproj y (hNK hy)).symm
  obtain ⟨P, hP, hPN, hPL⟩ := hlocal
  refine ⟨P, O'', hP, hO'', hxO'', ?_, hPL⟩
  rw [hPN]
  exact hON

end PoincareConjecture.M76
