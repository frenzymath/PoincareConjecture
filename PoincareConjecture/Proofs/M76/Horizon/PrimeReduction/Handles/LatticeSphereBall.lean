import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.BoundedSphereRegion
import PoincareConjecture.Proofs.M76.Brown.LocallyFlatSphereBalls
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.CoordinateBounds

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem isConnected_interior_and_closure_of_unitBallPair
    {X : Type*} [TopologicalSpace X] [T2Space X] {D S : Set X}
    (hD : IsCompact D) (hfront : frontier D = S) (hp : IsUnitBallPair V3 D S) :
    IsConnected (interior D) ∧ closure (interior D) = D := by
  obtain ⟨_, e, heb⟩ := hp
  have hiff (x : D) : (x : X) ∈ interior D ↔ (e x : V3) ∈ ball (0 : V3) 1 := by
    rw [← self_sdiff_frontier D, hfront, mem_ball_zero_iff]
    change ((x : X) ∈ D ∧ (x : X) ∉ S) ↔ ‖(e x : V3)‖ < 1
    have hle := mem_closedBall_zero_iff.mp (e x).property
    simp only [x.property, true_and]
    rw [heb x, mem_sphere_zero_iff_norm]
    exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
  let q : interior D ≃ₜ ball (0 : V3) 1 :=
    e.restrictSubsets interior_subset ball_subset_closedBall hiff
  have hconn : IsConnected (interior D) := by
    let : ConnectedSpace (ball (0 : V3) 1) := isConnected_iff_connectedSpace.mp
      ((convex_ball (0 : V3) 1).isConnected ⟨0, mem_ball_self zero_lt_one⟩)
    let : ConnectedSpace (interior D) := q.connectedSpace_iff.mpr inferInstance
    exact isConnected_iff_connectedSpace.mpr inferInstance
  let I : Set (closedBall (0 : V3) 1) := Subtype.val ⁻¹' ball (0 : V3) 1
  have hIimage : (Subtype.val : closedBall (0 : V3) 1 → V3) '' I = ball (0 : V3) 1 :=
    image_preimage_eq_of_subset (by
      intro x hx
      exact ⟨⟨x, ball_subset_closedBall hx⟩, rfl⟩)
  have hIclosure : closure I = univ := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hIimage,
      closure_ball (0 : V3) one_ne_zero]
    ext x
    simp only [mem_preimage, x.property, mem_univ]
  let g : closedBall (0 : V3) 1 → X := fun y => e.symm y
  have hg : Continuous g := continuous_subtype_val.comp e.symm.continuous
  have hgI : g '' I = interior D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : V3) ∈ ball (0 : V3) 1 := hy
      exact (hiff (e.symm y)).mpr (by simpa only [e.apply_symm_apply] using hy')
    · intro hx
      exact ⟨e ⟨x, interior_subset hx⟩, (hiff _).mp hx,
        congrArg Subtype.val (e.symm_apply_apply _)⟩
  refine ⟨hconn, Subset.antisymm (closure_minimal interior_subset hD.isClosed) ?_⟩
  intro x hx
  have him : x ∈ g '' closure I := by
    rw [hIclosure]
    exact ⟨e ⟨x, hx⟩, mem_univ _, congrArg Subtype.val (e.symm_apply_apply _)⟩
  rw [← hgI]
  exact image_closure_subset_closure_image hg him

private theorem ball_pair_image_of_injOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {D S : Set X} (hD : IsCompact D) (hpair : IsUnitBallPair V3 D S)
    {f : X → Y} (hf : Continuous f) (hi : InjOn f D) :
    IsUnitBallPair V3 (f '' D) (f '' S) := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let q := Equiv.Set.imageOfInjOn f D hi
  have hq : Continuous q := (hf.comp continuous_subtype_val).subtype_mk _
  let H : D ≃ₜ f '' D := hq.homeoOfEquivCompactToT2
  apply hpair.of_homeomorph (image_mono hpair.1) H.symm
  intro y
  have hy : f (H.symm y) = (y : Y) :=
    congrArg Subtype.val (H.apply_symm_apply y)
  constructor
  · rintro ⟨x, hx, hxy⟩
    have heq := hi (hpair.1 hx) (H.symm y).property (hxy.trans hy.symm)
    exact heq ▸ hx
  · intro hx
    exact ⟨H.symm y, hx, hy⟩

theorem ChartwisePLSphere.exists_lattice_ball_pair_with_lift
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S : Set (LatticeHandleAmbient ι κ L)}
    (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    ∃ Q : Set (LatticeHandleAmbient ι κ L), IsCompact Q ∧ frontier Q = S ∧
      IsUnitBallPair V3 Q S ∧ Q ⊆ interior (latticeHandleDomain ι κ L) ∧
      ∃ U : Set ((ι → ℝ) × (κ → ℝ)), IsOpen U ∧ IsConnected U ∧
        IsCompact (closure U) ∧ IsConnected (frontier U) ∧
        Q = (fun z : (ι → ℝ) × (κ → ℝ) =>
          (z.1, (QuotientAddGroup.mk z.2 : (κ → ℝ) ⧸ L.toAddSubgroup))) '' closure U ∧
        S = (fun z : (ι → ℝ) × (κ → ℝ) =>
          (z.1, (QuotientAddGroup.mk z.2 : (κ → ℝ) ⧸ L.toAddSubgroup))) '' frontier U := by
  classical
  let V := (ι → ℝ) × (κ → ℝ)
  let a : V ≃L[ℝ] V3 := ContinuousLinearEquiv.ofFinrankEq (by
    simpa only [V, Module.finrank_prod, Module.finrank_pi, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_fin] using hdim)
  let p : V →+ LatticeHandleAmbient ι κ L :=
    (AddMonoidHom.id (ι → ℝ)).prodMap (QuotientAddGroup.mk' L.toAddSubgroup)
  have hp : IsLocalHomeomorph p :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.id_prod.isLocalHomeomorph
  obtain ⟨l, hli, hl⟩ := s.exists_standard_lattice_lift ι κ L
  have hpl (x : sphere (0 : V3) 1) :
      p (l x) = (s.parametrization x : LatticeHandleAmbient ι κ L) := hl x
  let l' : C(sphere (0 : V3) 1, V3) := ⟨fun x => a (l x), a.continuous.comp l.continuous⟩
  have hl' (x : sphere (0 : V3) 1) :
      (p ∘ a.symm) (l' x) = (s.parametrization x : LatticeHandleAmbient ι κ L) := by
    simpa only [Function.comp_apply, l', ContinuousMap.coe_mk, a.symm_apply_apply] using hpl x
  obtain ⟨hflat⟩ := s.locallyFlat_lift he.compatible (fun x _ => he.cover x)
    (hp.comp a.symm.toHomeomorph.isLocalHomeomorph) l' (a.injective.comp hli) hl'
  obtain ⟨D₀, hD₀, hfront₀, hpair₀⟩ := hasBrownLocallyFlatSphereBalls _ ⟨hflat⟩
  obtain ⟨hconn₀, hreg₀⟩ :=
    isConnected_interior_and_closure_of_unitBallPair hD₀ hfront₀ hpair₀
  let U := a.symm '' interior D₀
  have hU : IsOpen U := a.symm.toHomeomorph.isOpenMap _ isOpen_interior
  have hUc : IsConnected U := hconn₀.image a.symm a.symm.continuous.continuousOn
  have hcl : closure U = a.symm '' D₀ := by
    change closure (a.symm.toHomeomorph '' interior D₀) = _
    rw [← a.symm.toHomeomorph.image_closure, hreg₀]
    rfl
  have hcompact : IsCompact (closure U) := hcl ▸ hD₀.image a.symm.continuous
  have hrange : a.symm '' range l' = range l := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (a.symm_apply_apply _).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨a (l z), ⟨z,rfl⟩, a.symm_apply_apply _⟩
  have hfront : frontier U = range l := by
    change frontier (a.symm.toHomeomorph '' interior D₀) = _
    rw [← a.symm.toHomeomorph.image_frontier]
    have hfi : frontier (interior D₀) = frontier D₀ := by
      rw [frontier, hreg₀, interior_interior, hD₀.isClosed.frontier_eq]
    rw [hfi, hfront₀]
    exact hrange
  have hclfront : frontier (closure U) = range l := by
    rw [hcl]
    change frontier (a.symm.toHomeomorph '' D₀) = _
    rw [← a.symm.toHomeomorph.image_frontier, hfront₀]
    exact hrange
  have hpT : InjOn p (range l) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    exact congrArg l (s.parametrization.injective
      (Subtype.ext ((hpl x).symm.trans (hxy.trans (hpl y)))))
  have hTc : IsConnected (range l) := by
    let : ConnectedSpace (sphere (0 : V3) 1) :=
      isConnected_iff_connectedSpace.mp (isConnected_sphere (by simp) (0 : V3) zero_le_one)
    exact isConnected_range l.continuous
  have hpinj : InjOn p (closure U) :=
    injOn_closure_of_injOn_connected_frontier p hU
      (hcompact.isBounded.subset subset_closure) hUc (hfront ▸ hTc) (hfront ▸ hpT)
  have himage : p '' range l = S := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      rw [hpl]
      exact (s.parametrization z).property
    · intro hx
      obtain ⟨z, hz⟩ := s.parametrization.surjective ⟨x,hx⟩
      exact ⟨l z, mem_range_self z, (hpl z).trans (congrArg Subtype.val hz)⟩
  have hpair : IsUnitBallPair V3 (closure U) (range l) := by
    rw [hcl, ← hrange]
    exact ball_pair_image_of_injOn hD₀ hpair₀ a.symm.continuous a.symm.injective.injOn
  refine ⟨p '' closure U, hcompact.image hp.continuous, ?_, ?_, ?_,
    U, hU, hUc, hcompact, hfront ▸ hTc, rfl, ?_⟩
  · rw [frontier_image_compact_of_localHomeomorph hp hcompact hpinj, hclfront, himage]
  · rw [← himage]
    exact ball_pair_image_of_injOn hcompact hpair hp.continuous hpinj
  · rintro _ ⟨x,hx,rfl⟩
    rw [latticeHandleDomain, interior_prod_eq, interior_univ,
      interior_closedBall _ one_ne_zero]
    refine ⟨mem_ball_zero_iff.mpr ?_, mem_univ _⟩
    change ‖x.1‖ < 1
    rw [pi_norm_lt_iff zero_lt_one]
    intro i
    let : Nonempty ι := ⟨i⟩
    have hTbound (y : V) (hy : y ∈ frontier U) : |y.1 i| < 1 := by
      have hyS : p y ∈ S := himage ▸ mem_image_of_mem p (hfront ▸ hy)
      have hyR := hSR hyS
      rw [latticeHandleDomain, interior_prod_eq, interior_univ,
        interior_closedBall _ one_ne_zero] at hyR
      have hnorm : ‖y.1‖ < 1 := mem_ball_zero_iff.mp hyR.1
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y.1 i).trans_lt hnorm
    let A : V →ᵃ[ℝ] ℝ :=
      ((LinearMap.proj i).comp (LinearMap.fst ℝ (ι → ℝ) (κ → ℝ))).toAffineMap
    have hv : 0 < A.linear (Pi.single i 1, 0) := by simp [A]
    have hupper : x.1 i < 1 := Dehn.affine_lt_on_closure_of_lt_frontier hU
      (hcompact.isBounded.subset subset_closure) A _ hv
      (fun y hy => (abs_lt.mp (hTbound y hy)).2) x hx
    have hnv : 0 < (-A).linear (-(Pi.single i 1, 0)) := by
      change 0 < -(A.linear (-((Pi.single i 1, 0) : V)))
      rw [map_neg, neg_neg]
      exact hv
    have hneg := Dehn.affine_lt_on_closure_of_lt_frontier hU
      (hcompact.isBounded.subset subset_closure) (-A) _ hnv
      (a := 1) (fun y hy => by
        change -y.1 i < 1
        linarith [(abs_lt.mp (hTbound y hy)).1]) x hx
    change -x.1 i < 1 at hneg
    rw [Real.norm_eq_abs]
    exact abs_lt.mpr ⟨by linarith, hupper⟩
  · change S = p '' frontier U
    rw [hfront, himage]

theorem ChartwisePLSphere.exists_lattice_ball_pair
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S : Set (LatticeHandleAmbient ι κ L)}
    (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L)) :
    ∃ Q : Set (LatticeHandleAmbient ι κ L), IsCompact Q ∧ frontier Q = S ∧
      IsUnitBallPair V3 Q S ∧ Q ⊆ interior (latticeHandleDomain ι κ L) := by
  obtain ⟨Q,hQ,hfront,hpair,hinside,_⟩ := s.exists_lattice_ball_pair_with_lift L he hdim hSR
  exact ⟨Q,hQ,hfront,hpair,hinside⟩

end PoincareConjecture.M76
