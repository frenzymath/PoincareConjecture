import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCapBoundaryChart
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeAffineHeightStep
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)

theorem exists_cap_affine_normal_coordinates (ell : V3 →ᴬ[ℝ] ℝ)
    (hell : ell.toAffineMap.linear ≠ 0) :
    ∃ a : V3 ≃ᴬ[ℝ] (ℝ × V2), ∀ x, (a x).1 = ell x := by
  obtain ⟨f, _, hfinv⟩ := ZeroChargeJoint.exists_affine_height_coordinates
    (E := V2) ell.toAffineMap hell (by simp) 0
  let q := (ContinuousLinearEquiv.prodComm ℝ V2 ℝ).toContinuousAffineEquiv
  refine ⟨f.symm.trans q, ?_⟩
  intro x
  change (f.symm x).2 = ell x
  have hx := hfinv x
  change (f.symm x).2 = ell x - 0 at hx
  simpa only [sub_zero] using hx

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_cap_boundary_restriction
    {K : Set X} (B : OpenPartialHomeomorph X (ℝ × E))
    (hhalf : ∀ y ∈ B.source, y ∈ K ↔ 0 ≤ (B y).1)
    (x : frontier K) :
    (∀ y ∈ B.source, y ∈ (interior K)ᶜ ↔ (B y).1 ≤ 0) ∧
    (∀ y ∈ B.source, y ∈ frontier K ↔ (B y).1 = 0) ∧
    ∃ b : OpenPartialHomeomorph (frontier K) E,
      b.source = Subtype.val ⁻¹' B.source ∧
      b.target = {z | (0, z) ∈ B.target} ∧
      (∀ y : frontier K, b y = (B y).2) ∧
      ∀ z ∈ b.target, (b.symm z : X) = B.symm (0, z) := by
  let ell := (ContinuousLinearMap.fst ℝ ℝ E).toContinuousAffineMap
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro hz
    have hv : ell.toAffineMap.linear (1, 0) = 1 := rfl
    rw [hz] at hv
    norm_num at hv
  have hfront := B.isImage_frontier_of_affine_nonneg ell hell hhalf
  have himage : B.IsImage K {z | 0 ≤ z.1} := fun {y} hy => (hhalf y hy).symm
  have hint : interior {z : ℝ × E | 0 ≤ z.1} = {z | 0 < z.1} := by
    change interior ((Prod.fst : ℝ × E → ℝ) ⁻¹' Ici 0) =
      (Prod.fst : ℝ × E → ℝ) ⁻¹' Ioi 0
    rw [← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst, interior_Ici]
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have heq := himage.interior.apply_mem_iff hy
    rw [hint] at heq
    change 0 < (B y).1 ↔ y ∈ interior K at heq
    change ¬y ∈ interior K ↔ (B y).1 ≤ 0
    exact heq.not.symm.trans not_lt
  · intro y hy
    exact (hfront.apply_mem_iff hy).symm
  · let a : E →ᴬ[ℝ] (ℝ × E) :=
      (0 : E →L[ℝ] ℝ).toContinuousAffineMap.prod
        (ContinuousLinearMap.id ℝ E).toContinuousAffineMap
    let r := (ContinuousLinearMap.snd ℝ ℝ E).toContinuousAffineMap
    obtain ⟨b, hbs, hbt, hbf, hbi⟩ := B.exists_affine_hypersurface_chart ell hfront a r
      (fun _ => rfl) (fun z hz => Prod.ext hz.symm rfl) (fun _ => rfl) x
    exact ⟨b, hbs, hbt, hbf, hbi⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in

theorem exists_cap_chart_rectangle {V : Set (ℝ × E)} (hV : IsOpen V)
    {z : E} (hz : (0, z) ∈ V) {eps : ℝ} (heps : 0 < eps) :
    ∃ (r : ℝ) (O : Set E), 0 < r ∧ r ≤ eps ∧ IsOpen O ∧ z ∈ O ∧
      Set.prod (Ioo (-r) r) O ⊆ V := by
  obtain ⟨J, O, hJ, h0J, hO, hzO, hJO⟩ := mem_nhds_prod_iff'.mp (hV.mem_nhds hz)
  obtain ⟨r0, hr0, hball⟩ := Metric.isOpen_iff.mp hJ 0 h0J
  let r := min r0 eps
  have hr : 0 < r := lt_min hr0 heps
  refine ⟨r, O, hr, min_le_right _ _, hO, hzO, ?_⟩
  intro p hp
  apply hJO
  refine ⟨hball ?_, hp.2⟩
  rw [Real.ball_eq_Ioo, zero_sub, zero_add]
  constructor
  · linarith [hp.1.1, min_le_left r0 eps]
  · exact hp.1.2.trans_le (min_le_left _ _)

theorem exists_marked_cap_chart_at_frontier
    {K : Set X} (hK : IsClosed K) (B : OpenPartialHomeomorph X (ℝ × E))
    (hhalf : ∀ y ∈ B.source, y ∈ K ↔ 0 ≤ (B y).1)
    (x : frontier K) (hx : (x : X) ∈ B.source)
    {eps : ℝ} (heps : 0 < eps) {U : Set ↥((interior K)ᶜ)} (hU : IsOpen U)
    (g : (frontier K × Ico (0 : ℝ) eps) ≃ₜ U)
    (hgzero : ∀ p : frontier K × Ico (0 : ℝ) eps,
      (p.2 : ℝ) = 0 → ((g p : ↥((interior K)ᶜ)) : X) = (p.1 : X))
    (hgS : ∀ p : frontier K × Ico (0 : ℝ) eps,
      ((g p : ↥((interior K)ᶜ)) : X) ∈ frontier K ↔ (p.2 : ℝ) = 0) :
    ∃ (r : ℝ) (O : Set E) (b : OpenPartialHomeomorph (frontier K) E)
        (H : OpenPartialHomeomorph X (ℝ × E)),
      0 < r ∧ r ≤ eps ∧ IsOpen O ∧ (B x).2 ∈ O ∧
      Set.prod (Ioo (-r) r) O ⊆ B.target ∧
      b.source = Subtype.val ⁻¹' B.source ∧
      b.target = {z | (0, z) ∈ B.target} ∧
      (∀ y : frontier K, b y = (B y).2) ∧
      (∀ z ∈ b.target, (b.symm z : X) = B.symm (0, z)) ∧
      H.target = Set.prod (Ioo (-r) r) O ∧
      H.source = B.symm '' Set.prod (Ico (0 : ℝ) r) O ∪
        {y | ∃ z ∈ O, ∃ t : Ico (0 : ℝ) eps,
          (t : ℝ) < r ∧ ((g (b.symm z, t) : ↥((interior K)ᶜ)) : X) = y} ∧
      (x : X) ∈ H.source ∧
      (∀ p : Set.prod (Ico (0 : ℝ) r) O,
        H (B.symm (p : ℝ × E)) = (p : ℝ × E)) ∧
      ∀ z ∈ O, ∀ t : Ico (0 : ℝ) eps, (t : ℝ) < r →
        H ((g (b.symm z, t) : ↥((interior K)ᶜ)) : X) = (-(t : ℝ), z) := by
  obtain ⟨hopp, hfront, b, hbs, hbt, hbf, hbi⟩ :=
    exists_cap_boundary_restriction B hhalf x
  have hx0 : (B x).1 = 0 := (hfront x hx).mp x.property
  have hxpair : B x = (0, (B x).2) := Prod.ext hx0 rfl
  have hxt : (0, (B x).2) ∈ B.target := hxpair ▸ B.map_source hx
  obtain ⟨r, O, hr, hre, hO, hxO, hrect⟩ := exists_cap_chart_rectangle B.open_target hxt heps
  have hcover : K ∪ (interior K)ᶜ = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ interior K
    · exact Or.inl (interior_subset hy)
    · exact Or.inr hy
  have hS : frontier K = K ∩ (interior K)ᶜ := hK.frontier_eq
  obtain ⟨H, hHt, hHs, hHpos, hHneg⟩ := exists_marked_cap_boundary_chart
    hK isOpen_interior.isClosed_compl hcover hS B hhalf hopp b hbt hbi
    hr hre hO ⟨(B x).2, hxO⟩ hrect hU g hgzero hgS
  let N := Set.prod (Ioc (-r) (0 : ℝ)) O
  let I := Ico (0 : ℝ) eps
  let j : N → frontier K × I := fun p => (b.symm (p : ℝ × E).2,
    ⟨-(p : ℝ × E).1, by
      constructor <;> linarith [p.property.1.1, p.property.1.2]⟩)
  have hnegRange : range (fun p : N => ((g (j p) : ↥((interior K)ᶜ)) : X)) =
      {y | ∃ z ∈ O, ∃ t : I, (t : ℝ) < r ∧
        ((g (b.symm z, t) : ↥((interior K)ᶜ)) : X) = y} := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p : ℝ × E).2, p.property.2, (j p).2,
        by change -(p : ℝ × E).1 < r; linarith [p.property.1.1], rfl⟩
    · rintro ⟨z, hz, t, ht, rfl⟩
      let p : N := ⟨(-(t : ℝ), z), ⟨⟨by linarith, by linarith [t.property.1]⟩, hz⟩⟩
      refine ⟨p, ?_⟩
      apply congrArg (fun q : frontier K × I => ((g q : ↥((interior K)ᶜ)) : X))
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact neg_neg (t : ℝ)
  have hsource : H.source = B.symm '' Set.prod (Ico (0 : ℝ) r) O ∪
      {y | ∃ z ∈ O, ∃ t : I, (t : ℝ) < r ∧
        ((g (b.symm z, t) : ↥((interior K)ᶜ)) : X) = y} := by
    rw [← hnegRange]
    exact hHs
  have hxH : (x : X) ∈ H.source := by
    rw [hsource]
    refine Or.inl ⟨B x, ?_, B.left_inv hx⟩
    exact ⟨⟨hx0.ge, by simpa only [hx0] using hr⟩, hxO⟩
  refine ⟨r, O, b, H, hr, hre, hO, hxO, hrect, hbs, hbt, hbf, hbi,
    hHt, hsource, hxH, hHpos, ?_⟩
  intro z hz t ht
  let p : N := ⟨(-(t : ℝ), z), ⟨⟨by linarith, by linarith [t.property.1]⟩, hz⟩⟩
  have hjp : j p = (b.symm z, t) := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact neg_neg (t : ℝ)
  have hp := hHneg p
  change H ((g (j p) : ↥((interior K)ᶜ)) : X) = (p : ℝ × E) at hp
  rw [hjp] at hp
  exact hp

end PoincareConjecture.M76
