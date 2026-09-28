import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.NonsphericalBoundary
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardDeckRegions









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

theorem frontier_image_compact_of_localHomeomorph
    {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) {K : Set X} (hK : IsCompact K)
    (hi : InjOn f K) : frontier (f '' K) = f '' frontier K := by
  have hinterior (x : X) (hx : x ∈ K) :
      f x ∈ interior (f '' K) ↔ x ∈ interior K := by
    constructor
    · intro hfx
      obtain ⟨B, hxB, hB⟩ := hf x
      have hBeq : (B : X → Y) = f := hB.symm
      let T := f '' (K \ B.source)
      have hT : IsClosed T := ((hK.diff B.open_source).image hf.continuous).isClosed
      have hxT : f x ∉ T := by
        rintro ⟨z, hz, hzx⟩
        exact hz.2 (hi hz.1 hx hzx ▸ hxB)
      apply mem_interior.mpr
      refine ⟨B.source ∩ f ⁻¹' Tᶜ ∩ f ⁻¹' interior (f '' K), ?_,
        (B.open_source.inter (hT.isOpen_compl.preimage hf.continuous)).inter
          (isOpen_interior.preimage hf.continuous), ⟨⟨hxB, hxT⟩, hfx⟩⟩
      rintro z ⟨⟨hzB, hzT⟩, hzf⟩
      obtain ⟨w, hw, hwz⟩ := interior_subset hzf
      have hwB : w ∈ B.source := by
        by_contra hn
        exact hzT ⟨w, ⟨hw, hn⟩, hwz⟩
      have hwz' : w = z := B.injOn hwB hzB (by simpa only [hBeq] using hwz)
      exact hwz' ▸ hw
    · intro hxint
      exact mem_interior.mpr ⟨f '' interior K, image_mono interior_subset,
        hf.isOpenMap _ isOpen_interior, mem_image_of_mem f hxint⟩
  rw [(hK.image hf.continuous).isClosed.frontier_eq, hK.isClosed.frontier_eq]
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hn⟩
    exact ⟨x, ⟨hx, fun h => hn ((hinterior x hx).mpr h)⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    exact ⟨mem_image_of_mem f hx, fun h => hn ((hinterior x hx).mp h)⟩

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_lattice_bounded_region
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {S : Set (LatticeHandleAmbient ι κ L)}
    (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ latticeHandleDomain ι κ L) :
    ∃ D : Set (LatticeHandleAmbient ι κ L),
      IsOpen D ∧ IsConnected D ∧ IsCompact (closure D) ∧
      frontier D = S ∧ frontier (closure D) = S ∧
      closure D ⊆ latticeHandleDomain ι κ L := by
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
  obtain ⟨U₀, _, hU₀, _, hUc₀, _, _, _, hfront₀, _, _, _, hcompact₀, hclfront₀, _⟩ :=
    hflat.exists_bounded_complement_components
  let U := a.symm '' U₀
  have hU : IsOpen U := a.symm.toHomeomorph.isOpenMap _ hU₀
  have hUc : IsConnected U := hUc₀.image a.symm a.symm.continuous.continuousOn
  have hcl : closure U = a.symm '' closure U₀ :=
    (a.symm.toHomeomorph.image_closure U₀).symm
  have hcompact : IsCompact (closure U) := hcl ▸ hcompact₀.image a.symm.continuous
  have hfront : frontier U = range l := by
    change frontier (a.symm.toHomeomorph '' U₀) = _
    rw [← a.symm.toHomeomorph.image_frontier, hfront₀]
    ext x
    simp only [mem_image, mem_range, l', ContinuousMap.coe_mk]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (a.symm_apply_apply _).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨a (l z), ⟨z, rfl⟩, a.symm_apply_apply _⟩
  have hclfront : frontier (closure U) = range l := by
    rw [hcl]
    change frontier (a.symm.toHomeomorph '' closure U₀) = _
    rw [← a.symm.toHomeomorph.image_frontier, hclfront₀]
    rw [← hfront₀, a.symm.toHomeomorph.image_frontier]
    exact hfront
  have hpT : InjOn p (range l) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    have hxy' : s.parametrization x = s.parametrization y :=
      Subtype.ext ((hl x).symm.trans (hxy.trans (hl y)))
    exact congrArg l (s.parametrization.injective hxy')
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
      obtain ⟨z, hz⟩ := s.parametrization.surjective ⟨x, hx⟩
      exact ⟨l z, mem_range_self z, (hl z).trans (congrArg Subtype.val hz)⟩
  have hDcl : closure (p '' U) = p '' closure U :=
    (image_closure_of_isCompact hcompact hp.continuous.continuousOn).symm
  refine ⟨p '' U, hp.isOpenMap _ hU, hUc.image p hp.continuous.continuousOn,
    hDcl ▸ hcompact.image hp.continuous, ?_, ?_, ?_⟩
  · rw [(hp.isOpenMap _ hU).frontier_eq, hDcl, ← hpinj.image_sdiff_subset subset_closure,
      ← hU.frontier_eq, hfront, himage]
  · rw [hDcl, frontier_image_compact_of_localHomeomorph hp hcompact hpinj,
      hclfront, himage]
  · rw [hDcl]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨mem_closedBall_zero_iff.mpr ?_, mem_univ _⟩
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    change ‖x.1 i‖ ≤ 1
    have hTbound (y : V) (hy : y ∈ frontier U) : |y.1 i| ≤ 1 := by
      have hyS : p y ∈ S := himage ▸ mem_image_of_mem p (hfront ▸ hy)
      have hnorm : ‖y.1‖ ≤ 1 := mem_closedBall_zero_iff.mp (hSR hyS).1
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y.1 i).trans hnorm
    let A : V →ᵃ[ℝ] ℝ :=
      ((LinearMap.proj i).comp (LinearMap.fst ℝ (ι → ℝ) (κ → ℝ))).toAffineMap
    have hv : 0 < A.linear (Pi.single i 1, 0) := by simp [A]
    have hupper : x.1 i ≤ 1 := hU.affine_le_on_closure_of_le_frontier
      (hcompact.isBounded.subset subset_closure) A _ hv
      (fun y hy => (abs_le.mp (hTbound y hy)).2) x hx
    have hnv : 0 < (-A).linear (-(Pi.single i 1, 0)) := by
      change 0 < -(A.linear (-((Pi.single i 1, 0) : V)))
      rw [map_neg, neg_neg]
      exact hv
    have hneg := hU.affine_le_on_closure_of_le_frontier
      (hcompact.isBounded.subset subset_closure) (-A) _ hnv
      (a := 1) (fun y hy => by
        change -y.1 i ≤ 1
        linarith [(abs_le.mp (hTbound y hy)).1]) x hx
    change -x.1 i ≤ 1 at hneg
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, hupper⟩

end PoincareConjecture.M76
