import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexBand
import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexHalfGeometry
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskPrismPasting
import PoincareConjecture.Proofs.M76.Mathlib.AffineHalfspaceSubcomplex

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "I+" => Icc (0 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  {T : OriginalProperDiskTriangulation e R j}
  {P : OriginalLowerProducts T} {p : (T.marked 2).vertices}

open Classical in

theorem OriginalVertexBand.exists_product (F : OriginalVertexBand P p) :
    ∃ H : (T.diskDualBase {(p : T.index → ℝ × V3)} ×ˢ I :
        Set ((T.index → ℝ × V3) × ℝ)) ≃ₜ T.dualRegion {(p : T.index → ℝ × V3)},
      H.IsFinitePL ∧
      (∀ (x : T.index → ℝ × V3) (hx : x ∈ T.diskDualBase {(p : T.index → ℝ × V3)}),
        (H ⟨(x, 0), ⟨hx, by norm_num, zero_le_one⟩⟩ : T.index → ℝ × V3) = x) ∧
      (∀ (x : (T.index → ℝ × V3) × ℝ)
        (hx : x ∈ (T.dualRegionRim {(p : T.index → ℝ × V3)} ∩ (T.marked 2).space) ×ˢ I),
        (H ⟨x, ⟨(T.vertex_base_ballPair p).1 hx.1, hx.2⟩⟩ : T.index → ℝ × V3) = F.map x) ∧
      ∀ x : (T.diskDualBase {(p : T.index → ℝ × V3)} ×ˢ I :
          Set ((T.index → ℝ × V3) × ℝ)),
        (H x : T.index → ℝ × V3) ∈ (T.marked 1).space ↔
          (x : (T.index → ℝ × V3) × ℝ).1 ∈ (T.marked 1).space := by
  classical
  let E := T.index → ℝ × V3
  let B := T.diskDualBase {(p : E)}
  let N := T.dualRegion {(p : E)}
  let Q := T.dualRegionRim {(p : E)}
  let q := Q ∩ (T.marked 2).space
  let h := T.height p
  let Np := N ∩ {x | 0 ≤ h x}
  let Nm := N ∩ {x | h x ≤ 0}
  let Sp := (Q ∩ {x | 0 ≤ h x}) ∪ B
  let Sm := (Q ∩ {x | h x ≤ 0}) ∪ B
  have hB : IsFinitePLBallPair (ℝ × ℝ) B q := T.vertex_base_ballPair p
  have hQN : Q ⊆ N := by
    have hq : Q = (((T.vertexBlock p).link p).space ∩ (T.marked 0).space) ∪
        ((T.vertexBlock p).space ∩ (T.marked 1).space) := by
      dsimp only [Q, OriginalProperDiskTriangulation.dualRegionRim]
      rw [Finset.centroid_singleton]
      rfl
    rw [hq]
    rintro x (hx | hx)
    · have hlink : (T.vertexBlock p).link p ≤ T.vertexBlock p := fun _ hs => hs.1
      exact ⟨SimplicialComplex.space_subset_of_le hlink hx.1, hx.2⟩
    · exact ⟨hx.1, T.boundary_space_subset_region hx.2⟩
  have hbase : B = N ∩ (T.marked 2).space := rfl
  have hbasezero (x : E) (hx : x ∈ N) : x ∈ B ↔ h x = 0 := by
    have he := T.height_eq_zero_iff_on_dualRegion p (Finset.mem_singleton_self _) hx
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
    (T.weight (T.chart_index p)) (T.weight_nonzero (T.chart_index p))
  change IsFinitePLBallPair C3 Np Sp at hpball
  change (Sp \ B).Nonempty at hpout
  have hmdata := T.vertex_half_ballPair_and_outside p
    (-T.weight (T.chart_index p)) (neg_ne_zero.mpr (T.weight_nonzero (T.chart_index p)))
  have hmdata' : IsFinitePLBallPair C3 Nm Sm ∧ (Sm \ B).Nonempty := by
    simpa only [Nm, Sm, h, B, N, Q, OriginalProperDiskTriangulation.height,
      neg_mul, neg_nonneg] using hmdata
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
  let r : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (-(ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hr : FinitePiecewiseAffineOn r (q ×ˢ I+) :=
    ⟨L, hL, hLspace, L.affineOnFaces_affine r⟩
  have hrmap : MapsTo r (q ×ˢ I+) (q ×ˢ I) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    change -x.2 ∈ I
    constructor <;> linarith [hx.2.1, hx.2.2]
  let Fm := F.map ∘ r
  have hFm : FinitePiecewiseAffineOn Fm (q ×ˢ I+) := F.piecewiseAffine.comp hr hrmap
  have him : InjOn Fm (q ×ˢ I+) := by
    intro x hx y hy he
    have he' := F.injective (hrmap hx) (hrmap hy) he
    change (x.1, -x.2) = (y.1, -y.2) at he'
    have hfirst := congrArg (fun z : E × ℝ => z.1) he'
    have hsecond := congrArg (fun z : E × ℝ => z.2) he'
    exact Prod.ext hfirst (neg_injective hsecond)
  have hFSp : MapsTo F.map (q ×ˢ I+) Sp := by
    intro x hx
    exact Or.inl ⟨F.inside (hplus hx), (F.positive x (hplus hx)).mpr hx.2.1⟩
  have hFSm : MapsTo Fm (q ×ˢ I+) Sm := by
    intro x hx
    exact Or.inl ⟨F.inside (hrmap hx),
      (F.negative (r x) (hrmap hx)).mpr (neg_nonpos.mpr hx.2.1)⟩
  have hFm0 (x : E) (hx : x ∈ q) : Fm (x, 0) = x := by
    change F.map (x, -(0 : ℝ)) = x
    rw [neg_zero]
    exact F.central x hx
  have hFmB (x : E × ℝ) (hx : x ∈ q ×ˢ I+) : Fm x ∈ B ↔ x.2 = 0 := by
    change F.map (r x) ∈ B ↔ x.2 = 0
    rw [hcontact _ (hrmap hx)]
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
    have hyF : y.1 ∈ (T.marked 1).space := (F.proper y hy).mp (hyx.symm ▸ hxF)
    exact congrArg Prod.fst hey ▸ hyF
  · intro hxF
    have hxq : (x : E × ℝ).1 ∈ q := by
      rw [show q = T.dualRegionRim {(p : E)} ∩ (T.marked 2).space from rfl,
        T.vertex_base_rim_eq]
      exact Or.inr ⟨x.property.1, hxF⟩
    rw [hside (x : E × ℝ) ⟨hxq, x.property.2⟩]
    exact (F.proper x ⟨hxq, x.property.2⟩).mpr hxF

end PoincareConjecture.M76
