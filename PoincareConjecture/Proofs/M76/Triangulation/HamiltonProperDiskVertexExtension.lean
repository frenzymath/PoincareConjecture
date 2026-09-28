import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBand
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexHalfGeometry
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskPrismPasting
import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "I+" => Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}
  {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] (V2 × ℝ)}
  {C : HamiltonProperDiskCoherentSides T c}
  {P : HamiltonProperDiskLowerProducts T C} {p : T.disk.vertices}

theorem HamiltonProperDiskVertexBand.exists_product
    (F : HamiltonProperDiskVertexBand P p) :
    ∃ H : (T.diskVertexBlock p ×ˢ I : Set (E × ℝ)) ≃ₜ T.dualRegion {(p : E)},
      H.IsFinitePL ∧
      (∀ (x : E) (hx : x ∈ T.diskVertexBlock p),
        (H ⟨(x, 0), ⟨hx, by norm_num, zero_le_one⟩⟩ : E) = x) ∧
      (∀ (x : E × ℝ) (hx : x ∈ (T.dualRegionRim {(p : E)} ∩ D) ×ˢ I),
        (H ⟨x, ⟨(T.vertex_base_ballPair p).1 hx.1, hx.2⟩⟩ : E) = F.map x) ∧
      ∀ x : (T.diskVertexBlock p ×ˢ I : Set (E × ℝ)),
        (H x : E) ∈ frontier R ↔ (x : E × ℝ).1 ∈ frontier R := by
  classical
  let B := T.diskVertexBlock p
  let N := T.dualRegion {(p : E)}
  let Q := T.dualRegionRim {(p : E)}
  let q := Q ∩ D
  let h := C.labels.height p
  let Np := N ∩ {x | 0 ≤ h x}
  let Nm := N ∩ {x | h x ≤ 0}
  let Sp := (Q ∩ {x | 0 ≤ h x}) ∪ B
  let Sm := (Q ∩ {x | h x ≤ 0}) ∪ B
  have hB : IsFinitePLBallPair (ℝ × ℝ) B q := T.vertex_base_ballPair p
  have hRclosed : IsClosed R := by
    rw [← T.region_space]
    exact (T.region.isCompact_space_of_finite (T.finite.subset T.region_le)).isClosed
  have hQN : Q ⊆ N := by
    have hq : Q = (((T.vertexBlock p).link p).space ∩ R) ∪
        ((T.vertexBlock p).space ∩ frontier R) := by
      simp only [Q, HamiltonProperDiskTriangulation.dualRegionRim,
        Finset.centroid_singleton, id_eq, HamiltonProperDiskTriangulation.vertexBlock]
    rw [hq]
    rintro x (hx | hx)
    · have hlink : (T.vertexBlock p).link p ≤ T.vertexBlock p := fun _ hs => hs.1
      exact ⟨SimplicialComplex.space_subset_of_le hlink hx.1, hx.2⟩
    · exact ⟨hx.1, hRclosed.frontier_subset hx.2⟩
  have hbase : B = N ∩ D := by
    rw [show B = (T.vertexBlock p).space ∩ D from T.diskVertexBlock_eq_inter p]
    ext x
    change (x ∈ (T.vertexBlock p).space ∧ x ∈ D) ↔
      (x ∈ (T.vertexBlock p).space ∧ x ∈ R) ∧ x ∈ D
    constructor
    · exact fun hx => ⟨⟨hx.1, T.disk_subset_region hx.2⟩, hx.2⟩
    · exact fun hx => ⟨hx.1.1, hx.2⟩
  have hbasezero (x : E) (hx : x ∈ N) : x ∈ B ↔ h x = 0 := by
    have he := C.labels.height_eq_zero_iff p
      (T.dualRegion_subset_chart_source p (Finset.mem_singleton_self _) hx) hx.2
    rw [hbase]
    exact (and_iff_right hx).trans he.symm
  have hcontact (x : E × ℝ) (hx : x ∈ q ×ˢ I) : F.map x ∈ B ↔ x.2 = 0 := by
    rw [hbasezero _ (hQN (F.inside hx))]
    constructor
    · intro he
      exact le_antisymm ((F.negative x hx).mp he.le) ((F.positive x hx).mp he.ge)
    · intro ht
      exact le_antisymm ((F.negative x hx).mpr ht.le) ((F.positive x hx).mpr ht.ge)
  obtain ⟨hpball, hpout⟩ := T.vertex_half_ballPair_and_outside p
    (C.labels.weight p) (C.labels.nonzero p)
  change IsFinitePLBallPair V Np Sp at hpball
  change (Sp \ B).Nonempty at hpout
  have hmdata := T.vertex_half_ballPair_and_outside p
    (-C.labels.weight p) (neg_ne_zero.mpr (C.labels.nonzero p))
  have hmdata' : IsFinitePLBallPair V Nm Sm ∧ (Sm \ B).Nonempty := by
    simpa only [Nm, Sm, h, B, N, Q, HamiltonProperDiskNormalLabels.height,
      neg_mul, neg_nonneg]
      using hmdata
  obtain ⟨hmball, hmout⟩ := hmdata'
  have hplus : q ×ˢ I+ ⊆ q ×ˢ I := fun _ hx =>
    ⟨hx.1, (by linarith [hx.2.1]), hx.2.2⟩
  obtain ⟨K, hK, hKs, _⟩ := F.piecewiseAffine
  let a : (E × ℝ) →ᵃ[ℝ] ℝ :=
    -(ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap.toAffineMap
  obtain ⟨L, hL, hLs⟩ := K.exists_finite_triangulation_inter_halfspaces hK {a}
  have hLspace : L.space = q ×ˢ I+ := by
    rw [hLs, hKs]
    ext x
    simp only [Finset.mem_singleton, forall_eq, mem_inter_iff, mem_prod, mem_Icc]
    change (((x.1 ∈ q ∧ -1 ≤ x.2 ∧ x.2 ≤ 1) ∧ -x.2 ≤ 0) ↔
      (x.1 ∈ q ∧ 0 ≤ x.2 ∧ x.2 ≤ 1))
    constructor
    · exact fun hx => ⟨hx.1.1, neg_nonpos.mp hx.2, hx.1.2.2⟩
    · exact fun hx => ⟨⟨hx.1, (by linarith [hx.2.1]), hx.2.2⟩,
        neg_nonpos.mpr hx.2.1⟩
  have hFp : FinitePiecewiseAffineOn F.map (q ×ˢ I+) := by
    rw [← hLspace]
    exact F.piecewiseAffine.restrict L hL (hLspace.subset.trans hplus)
  let j : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (-(ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hj : FinitePiecewiseAffineOn j (q ×ˢ I+) :=
    ⟨L, hL, hLspace, L.affineOnFaces_affine j⟩
  have hjmap : MapsTo j (q ×ˢ I+) (q ×ˢ I) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    change -x.2 ∈ I
    constructor <;> linarith [hx.2.1, hx.2.2]
  let Fm := F.map ∘ j
  have hFm : FinitePiecewiseAffineOn Fm (q ×ˢ I+) := F.piecewiseAffine.comp hj hjmap
  have him : InjOn Fm (q ×ˢ I+) := by
    intro x hx y hy he
    have he' := F.injective (hjmap hx) (hjmap hy) he
    change (x.1, -x.2) = (y.1, -y.2) at he'
    have hfirst := congrArg (fun z : E × ℝ => z.1) he'
    have hsecond := congrArg (fun z : E × ℝ => z.2) he'
    exact Prod.ext hfirst (neg_injective hsecond)
  have hFSp : MapsTo F.map (q ×ˢ I+) Sp := by
    intro x hx
    exact Or.inl ⟨F.inside (hplus hx), (F.positive x (hplus hx)).mpr hx.2.1⟩
  have hFSm : MapsTo Fm (q ×ˢ I+) Sm := by
    intro x hx
    exact Or.inl ⟨F.inside (hjmap hx),
      (F.negative (j x) (hjmap hx)).mpr (neg_nonpos.mpr hx.2.1)⟩
  have hFm0 (x : E) (hx : x ∈ q) : Fm (x, 0) = x := by
    change F.map (x, -(0 : ℝ)) = x
    rw [neg_zero]
    exact F.central x hx
  have hFmB (x : E × ℝ) (hx : x ∈ q ×ˢ I+) : Fm x ∈ B ↔ x.2 = 0 := by
    change F.map (j x) ∈ B ↔ x.2 = 0
    rw [hcontact _ (hjmap hx)]
    change -x.2 = 0 ↔ x.2 = 0
    exact neg_eq_zero
  obtain ⟨HP, hHP, hHP0, hHPSide, _, _⟩ := hpball.exists_disk_prism_extension hB
    subset_union_right hpout F.map hFp (F.injective.mono hplus) hFSp F.central
    (fun x hx => hcontact x (hplus hx))
  obtain ⟨HM, hHM, hHM0, hHMSide, _, _⟩ := hmball.exists_disk_prism_extension hB
    subset_union_right hmout Fm hFm him hFSm hFm0 hFmB
  have hmeet : Nm ∩ Np = B := by
    ext x
    constructor
    · intro hx
      exact (hbasezero x hx.1.1).mpr (le_antisymm hx.1.2 hx.2.2)
    · intro hx
      have hxN := (hbase.subset hx).1
      have hz := (hbasezero x hxN).mp hx
      exact ⟨⟨hxN, hz.le⟩, hxN, hz.ge⟩
  have hcover : Nm ∪ Np = N := by
    ext x
    constructor
    · exact fun hx => hx.elim And.left And.left
    · intro hx
      exact (le_total (h x) 0).elim (fun hz => Or.inl ⟨hx, hz⟩)
        (fun hz => Or.inr ⟨hx, hz⟩)
  obtain ⟨H, hH, hkeepP, hkeepM⟩ :=
    hB.exists_two_sided_disk_prism HM HP hHM hHP hHM0 hHP0 hmeet hcover
  have hcenter (x : E) (hx : x ∈ B) :
      (H ⟨(x, 0), ⟨hx, by norm_num, zero_le_one⟩⟩ : E) = x :=
    (hkeepP (x, 0) ⟨hx, le_rfl, zero_le_one⟩).trans (hHP0 x hx)
  have hside (x : E × ℝ) (hx : x ∈ q ×ˢ I) :
      (H ⟨x, ⟨hB.1 hx.1, hx.2⟩⟩ : E) = F.map x := by
    by_cases ht : 0 ≤ x.2
    · exact (hkeepP x ⟨hB.1 hx.1, ht, hx.2.2⟩).trans
        (hHPSide x ⟨hx.1, ht, hx.2.2⟩)
    · have ht' : x.2 ≤ 0 := (lt_of_not_ge ht).le
      have hy : (x.1, -x.2) ∈ q ×ˢ I+ :=
        ⟨hx.1, neg_nonneg.mpr ht', by linarith [hx.2.1]⟩
      have hval := (hkeepM x ⟨hB.1 hx.1, hx.2.1, ht'⟩).trans
        (hHMSide (x.1, -x.2) hy)
      have hvalue : Fm (x.1, -x.2) = F.map x := by
        change F.map (x.1, - -x.2) = F.map x
        simp only [neg_neg, Prod.mk.eta]
      exact hval.trans hvalue
  refine ⟨H, hH, hcenter, hside, ?_⟩
  intro x
  constructor
  · intro hxF
    obtain ⟨y, hy, hyx⟩ := F.frontier_image_subset ⟨(H x).property.1, hxF⟩
    have he : H ⟨y, ⟨hB.1 hy.1, hy.2⟩⟩ = H x :=
      Subtype.ext ((hside y hy).trans hyx)
    have hey : y = (x : E × ℝ) := congrArg Subtype.val (H.injective he)
    have hyF : y.1 ∈ frontier R := (F.proper y hy).mp (hyx.symm ▸ hxF)
    exact congrArg Prod.fst hey ▸ hyF
  · intro hxF
    have hxq : (x : E × ℝ).1 ∈ q := by
      rw [show q = T.dualRegionRim {(p : E)} ∩ D from rfl, T.vertex_base_rim_eq]
      exact Or.inr ⟨x.property.1, hxF⟩
    rw [hside (x : E × ℝ) ⟨hxq, x.property.2⟩]
    exact (F.proper x ⟨hxq, x.property.2⟩).mpr hxF

end PoincareConjecture.M76.HamiltonIndexOne
