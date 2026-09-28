import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCapBoundaryNeighborhood
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedCapCoordinates










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)

variable {X : Type*} [TopologicalSpace X] {Y : Set X} {ι : Type*}






theorem PLDomain.exists_normalized_cap_chart_in_open_ambient
    (hY : IsOpen Y) {e : ι → OpenPartialHomeomorph Y V3} {K : Set Y}
    (hKD : PLDomain e K) {D : Set X} (y : Y) (hy : y ∈ frontier K)
    (N : Set Y) (hN : IsOpen N) (hyN : y ∈ N)
    (hlocal : ∀ z ∈ N, (z : X) ∈ D ↔ z ∉ interior K) :
    ∃ (B0 : OpenPartialHomeomorph Y V3) (a : V3 ≃ᴬ[ℝ] (ℝ × V2))
        (C : OpenPartialHomeomorph X (ℝ × V2)),
      (∀ i, (e i).symm.trans B0 ∈ Geometry.piecewiseAffineGroupoid V3) ∧
      C.source = (Subtype.val : Y → X) '' (B0.source ∩ N) ∧
      (∀ z : Y, z ∈ B0.source ∩ N → C z = a (B0 z)) ∧
      (∀ z ∈ C.target, a.symm z ∈ B0.target ∧
        B0.symm (a.symm z) ∈ N ∧ C.symm z = (B0.symm (a.symm z) : X)) ∧
      (y : X) ∈ C.source ∧ (C y).1 = 0 ∧
      (∀ z ∈ C.source, z ∈ D ↔ (C z).1 ≤ 0) ∧
      (∀ z ∈ C.source, z ∈ (interior D)ᶜ ↔ 0 ≤ (C z).1) ∧
      ∀ z ∈ C.source, z ∈ frontier D ↔ (C z).1 = 0 := by
  classical
  let : Nonempty Y := ⟨y⟩
  let j : OpenPartialHomeomorph Y X :=
    hY.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : Y → X)
  have hjs : j.source = univ := rfl
  obtain ⟨ell, v, B0, hv, hyB0, hy0, hcompat, hhalf⟩ := hKD.halfspace y hy
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro hz
    have hv' : ell.toAffineMap.linear v = 1 := hv
    rw [hz] at hv'
    norm_num at hv'
  obtain ⟨a, ha⟩ := exists_cap_affine_normal_coordinates ell hell
  let B := B0.restrOpen N hN
  let C := (j.symm.trans B).transHomeomorph a.toHomeomorph
  have hCs : C.source = (Subtype.val : Y → X) '' (B0.source ∩ N) := by
    ext z
    constructor
    · intro hz
      exact ⟨j.symm z, hz.2, j.right_inv hz.1⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨j.map_source (hjs.symm ▸ mem_univ z), ?_⟩
      change j.symm (j z) ∈ B.source
      rw [j.left_inv (hjs.symm ▸ mem_univ z)]
      exact hz
  have hCval (z : Y) (hz : z ∈ B0.source ∩ N) : C z = a (B0 z) := by
    change a (B (j.symm (j z))) = a (B0 z)
    rw [j.left_inv (hjs.symm ▸ mem_univ z)]
    rfl
  have hCinv (z : ℝ × V2) (hz : z ∈ C.target) : a.symm z ∈ B0.target ∧
      B0.symm (a.symm z) ∈ N ∧ C.symm z = (B0.symm (a.symm z) : X) := by
    have hzB : a.symm z ∈ B.target := hz.1
    exact ⟨hzB.1, hzB.2, rfl⟩
  have hyC : (y : X) ∈ C.source := hCs.symm ▸ ⟨y, ⟨hyB0, hyN⟩, rfl⟩
  have hyC0 : (C y).1 = 0 := by rw [hCval y ⟨hyB0, hyN⟩, ha, hy0]
  have hBD : ∀ z ∈ C.source, z ∈ D ↔ (C z).1 ≤ 0 := by
    intro z hz
    have hzj : z ∈ j.target := hz.1
    have hzB : j.symm z ∈ B.source := hz.2
    have hjval : (j.symm z : X) = z := j.right_inv hzj
    have himage : B.IsImage K {w | 0 ≤ ell w} := by
      intro w hw
      exact (hhalf w hw.1).symm
    have hopen : IsOpenMap (ell : V3 → ℝ) := ell.toAffineMap.isOpenMap ell.continuous
      (ell.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective hell))
    have hint : interior {w | 0 ≤ ell w} = {w | 0 < ell w} := by
      change interior ((ell : V3 → ℝ) ⁻¹' Ici 0) = (ell : V3 → ℝ) ⁻¹' Ioi 0
      rw [← hopen.preimage_interior_eq_interior_preimage ell.continuous, interior_Ici]
    have hBi := himage.interior.apply_mem_iff hzB
    rw [hint] at hBi
    change 0 < ell (B (j.symm z)) ↔ j.symm z ∈ interior K at hBi
    change z ∈ D ↔ (a (B (j.symm z))).1 ≤ 0
    rw [ha]
    have hlocal' : z ∈ D ↔ j.symm z ∉ interior K := by
      simpa only [hjval] using hlocal (j.symm z) hzB.2
    exact hlocal'.trans (hBi.not.symm.trans not_lt)
  have hDi : C.IsImage D {z | z.1 ≤ 0} := fun {z} hz => (hBD z hz).symm
  have hpos : ∀ z ∈ C.source, z ∈ (interior D)ᶜ ↔ 0 ≤ (C z).1 := by
    have hint : interior {z : ℝ × V2 | z.1 ≤ 0} = {z | z.1 < 0} := by
      change interior ((Prod.fst : ℝ × V2 → ℝ) ⁻¹' Iic 0) =
        (Prod.fst : ℝ × V2 → ℝ) ⁻¹' Iio 0
      rw [← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst, interior_Iic]
    intro z hz
    have hi := hDi.interior.apply_mem_iff hz
    rw [hint] at hi
    change (C z).1 < 0 ↔ z ∈ interior D at hi
    exact hi.not.symm.trans not_lt
  have hfront : ∀ z ∈ C.source, z ∈ frontier D ↔ (C z).1 = 0 := by
    have hf : frontier {z : ℝ × V2 | z.1 ≤ 0} = {z | z.1 = 0} := by
      change frontier ((Prod.fst : ℝ × V2 → ℝ) ⁻¹' Iic 0) =
        (Prod.fst : ℝ × V2 → ℝ) ⁻¹' {0}
      rw [← isOpenMap_fst.preimage_frontier_eq_frontier_preimage continuous_fst, frontier_Iic]
    intro z hz
    have hh := hDi.frontier.apply_mem_iff hz
    rw [hf] at hh
    exact hh.symm
  exact ⟨B0, a, C, hcompat, hCs, hCval, hCinv, hyC, hyC0, hBD, hpos, hfront⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in




theorem exists_marked_cap_coordinates_of_closed_sides
    {K D S : Set X} (hK : IsClosed K) (hD : IsClosed D)
    (hcover : K ∪ D = univ) (hS : S = K ∩ D)
    (C : OpenPartialHomeomorph X (ℝ × E))
    (hCK : ∀ z ∈ C.source, z ∈ K ↔ 0 ≤ (C z).1)
    (hCD : ∀ z ∈ C.source, z ∈ D ↔ (C z).1 ≤ 0)
    (x : S) (hx : (x : X) ∈ C.source)
    {eps : ℝ} (heps : 0 < eps) {U : Set D} (hU : IsOpen U)
    (g : (S × Ico (0 : ℝ) eps) ≃ₜ U)
    (hgzero : ∀ p : S × Ico (0 : ℝ) eps,
      (p.2 : ℝ) = 0 → ((g p : D) : X) = (p.1 : X))
    (hgS : ∀ p : S × Ico (0 : ℝ) eps,
      ((g p : D) : X) ∈ S ↔ (p.2 : ℝ) = 0) :
    ∃ c : HamiltonMarkedCapCoordinates (E := E) (D := D) (fun p => ((g p : D) : X)),
      c.original = C ∧ (x : X) ∈ c.chart.source := by
  let ell := (ContinuousLinearMap.fst ℝ ℝ E).toContinuousAffineMap
  have himage : C.IsImage S {z | ell z = 0} := by
    intro z hz
    change (C z).1 = 0 ↔ z ∈ S
    rw [hS, mem_inter_iff, hCK z hz, hCD z hz]
    exact ⟨fun h => ⟨h.ge, h.le⟩, fun h => le_antisymm h.2 h.1⟩
  let a : E →ᴬ[ℝ] (ℝ × E) :=
    (0 : E →L[ℝ] ℝ).toContinuousAffineMap.prod
      (ContinuousLinearMap.id ℝ E).toContinuousAffineMap
  let r0 := (ContinuousLinearMap.snd ℝ ℝ E).toContinuousAffineMap
  obtain ⟨b, hbs, hbt, hbf, hbi⟩ := C.exists_affine_hypersurface_chart ell himage a r0
    (fun _ => rfl) (fun z hz => Prod.ext hz.symm rfl) (fun _ => rfl) x
  have hx0 : (C x).1 = 0 := (himage.apply_mem_iff hx).mpr x.property
  have hxpair : C x = (0, (C x).2) := Prod.ext hx0 rfl
  obtain ⟨r, O, hr, hre, hO, hxO, hrect⟩ := exists_cap_chart_rectangle C.open_target
    (hxpair ▸ C.map_source hx) heps
  obtain ⟨H, hHt, hHs, hHpos, hHneg⟩ := exists_marked_cap_boundary_chart
    hK hD hcover hS C hCK hCD b hbt hbi hr hre hO ⟨(C x).2, hxO⟩ hrect
    hU g hgzero hgS
  let N := Set.prod (Ioc (-r) (0 : ℝ)) O
  let I := Ico (0 : ℝ) eps
  let j : N → S × I := fun p => (b.symm (p : ℝ × E).2,
    ⟨-(p : ℝ × E).1, by
      constructor <;> linarith [p.property.1.1, p.property.1.2]⟩)
  have hnegRange : range (fun p : N => ((g (j p) : D) : X)) =
      {y | ∃ z ∈ O, ∃ t : I, (t : ℝ) < r ∧ ((g (b.symm z, t) : D) : X) = y} := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p : ℝ × E).2, p.property.2, (j p).2,
        by change -(p : ℝ × E).1 < r; linarith [p.property.1.1], rfl⟩
    · rintro ⟨z, hz, t, ht, rfl⟩
      let p : N := ⟨(-(t : ℝ), z), ⟨⟨by linarith, by linarith [t.property.1]⟩, hz⟩⟩
      refine ⟨p, ?_⟩
      apply congrArg (fun q : S × I => ((g q : D) : X))
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact neg_neg (t : ℝ)
  have hsource : H.source = C.symm '' Set.prod (Ico (0 : ℝ) r) O ∪
      {y | ∃ z ∈ O, ∃ t : I, (t : ℝ) < r ∧ ((g (b.symm z, t) : D) : X) = y} := by
    rw [← hnegRange]
    exact hHs
  have hxH : (x : X) ∈ H.source := by
    rw [hsource]
    refine Or.inl ⟨C x, ?_, C.left_inv hx⟩
    exact ⟨⟨hx0.ge, by simpa only [hx0] using hr⟩, hxO⟩
  have hnegative : ∀ z ∈ O, ∀ t : I, (t : ℝ) < r →
      H ((g (b.symm z, t) : D) : X) = (-(t : ℝ), z) := by
    intro z hz t ht
    let p : N := ⟨(-(t : ℝ), z), ⟨⟨by linarith, by linarith [t.property.1]⟩, hz⟩⟩
    have hjp : j p = (b.symm z, t) := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact neg_neg (t : ℝ)
    have hp := hHneg p
    change H ((g (j p) : D) : X) = (p : ℝ × E) at hp
    rw [hjp] at hp
    exact hp
  let c : HamiltonMarkedCapCoordinates (E := E) (D := D) (fun p => ((g p : D) : X)) := {
    original := C
    boundary := b
    chart := H
    radius := r
    lateral := O
    radius_pos := hr
    radius_le := hre
    lateral_open := hO
    rectangle := hrect
    boundary_source := hbs
    boundary_target := hbt
    boundary_forward := hbf
    boundary_inverse := hbi
    original_side := hCD
    target := hHt
    source := hsource
    positive := hHpos
    negative := hnegative }
  exact ⟨c, rfl, hxH⟩





theorem PLDomain.exists_marked_cap_coordinates_in_open_ambient
    (hY : IsOpen Y) {e : ι → OpenPartialHomeomorph Y V3} {K : Set Y}
    (hKD : PLDomain e K) {D : Set X} (hD : IsClosed D)
    (y : Y) (hy : y ∈ frontier K) (N : Set Y) (hN : IsOpen N) (hyN : y ∈ N)
    (hlocal : ∀ z ∈ N, (z : X) ∈ D ↔ z ∉ interior K)
    {eps : ℝ} (heps : 0 < eps) {U : Set D} (hU : IsOpen U)
    (g : (frontier D × Ico (0 : ℝ) eps) ≃ₜ U)
    (hgzero : ∀ p : frontier D × Ico (0 : ℝ) eps,
      (p.2 : ℝ) = 0 → ((g p : D) : X) = (p.1 : X))
    (hgS : ∀ p : frontier D × Ico (0 : ℝ) eps,
      ((g p : D) : X) ∈ frontier D ↔ (p.2 : ℝ) = 0) :
    ∃ (B0 : OpenPartialHomeomorph Y V3) (a : V3 ≃ᴬ[ℝ] (ℝ × V2))
        (c : HamiltonMarkedCapCoordinates (E := V2) (D := D) (fun p => ((g p : D) : X))),
      (∀ i, (e i).symm.trans B0 ∈ Geometry.piecewiseAffineGroupoid V3) ∧
      c.original.source = (Subtype.val : Y → X) '' (B0.source ∩ N) ∧
      (∀ z : Y, z ∈ B0.source ∩ N → c.original z = a (B0 z)) ∧
      (∀ z ∈ c.original.target, a.symm z ∈ B0.target ∧
        B0.symm (a.symm z) ∈ N ∧ c.original.symm z = (B0.symm (a.symm z) : X)) ∧
      (y : X) ∈ c.chart.source := by
  obtain ⟨B0, a, C, hcompat, hCs, hCval, hCinv, hyC, hy0, hCD, hCK, hfront⟩ :=
    hKD.exists_normalized_cap_chart_in_open_ambient hY y hy N hN hyN hlocal
  have hyS : (y : X) ∈ frontier D := (hfront y hyC).mpr hy0
  have hcover : (interior D)ᶜ ∪ D = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z ∈ interior D
    · exact Or.inr (interior_subset hz)
    · exact Or.inl hz
  have hS : frontier D = (interior D)ᶜ ∩ D := by
    rw [hD.frontier_eq]
    exact inter_comm _ _
  obtain ⟨c, hc, hyc⟩ := exists_marked_cap_coordinates_of_closed_sides
    isOpen_interior.isClosed_compl hD hcover hS C hCK hCD ⟨y, hyS⟩ hyC
    heps hU g hgzero hgS
  exact ⟨B0, a, c, hcompat, hc.symm ▸ hCs, hc.symm ▸ hCval,
    hc.symm ▸ hCinv, hyc⟩

end PoincareConjecture.M76
