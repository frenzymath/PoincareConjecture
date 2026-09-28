import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcCoveredBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CornerFrontierLines
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.PolygonalCores







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open Poincare.Topology.Plane.Meshes ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_exists_two_arc_remainder_mesh
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hareg : ∀ t ∈ Ioo (0 : ℝ) A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo (0 : ℝ) B, deriv beta t ≠ 0)
    (hinter : (alpha '' Icc 0 A) ∩ (beta '' Icc 0 B) ⊆ {alpha 0, alpha A})
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hind0 : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U) (hcompact : IsCompact (closure U)) :
    ∃ (H : Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : Bool → ℝ)
      (F : Bool → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (W : Bool → Set AnnulusCoordinates) (positive : Bool → Bool),
      let C (e : Bool) (i : Bool × Bool) :=
        F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
      let D (e : Bool) := ⋃ i,
        ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)), C e i
      (∀ e : Bool,
        0 < r e ∧ r e ≤ min A B / 3 ∧ (0 : ℝ × ℝ) ∈ (H e).source ∧
        H e 0 = alpha (if e then A else 0) ∧
        ContDiffOn ℝ ∞ (H e) (H e).source ∧ ContDiffOn ℝ ∞ (H e).symm (H e).target ∧
        (∀ s : ℝ, H e (s, 0) = alpha (if e then A - s else s)) ∧
        (∀ s : ℝ, H e (0, s) = beta (if e then B - s else s)) ∧
        (∀ i : Bool × Bool, ∀ s ∈ Icc (0 : ℝ) (r e),
          sectorParameterEquiv 0 i (s, 0) ∈ (H e).source ∧
          sectorParameterEquiv 0 i (0, s) ∈ (H e).source) ∧
        (∀ q ∈ (H e).source, H e q ∈ frontier U ↔
          (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0)) ∧
        (∀ q ∈ (H e).source, H e q ∈ closure U ↔
          if positive e then 0 ≤ q.1 ∧ 0 ≤ q.2 else q.1 ≤ 0 ∨ q.2 ≤ 0) ∧
        (∀ i,
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆ (F e i).source ∧
          (F e i).target ⊆ (H e).target ∧
          ContDiffOn ℝ ∞ (F e i) (F e i).source ∧
          ContDiffOn ℝ ∞ (F e i).symm (F e i).target ∧
          (∀ s ∈ Icc (0 : ℝ) (r e), F e i (s, 0) = H e (sectorParameterEquiv 0 i (s, 0))) ∧
          (∀ s ∈ Icc (0 : ℝ) (r e), F e i (0, s) = H e (sectorParameterEquiv 0 i (0, s))) ∧
          (∀ t : ℝ, F e i ((1 - t) * r e, t * r e) =
            (1 - t) • F e i (r e, 0) + t • F e i (0, r e)) ∧
          C e i ⊆ H e '' ((H e).source ∩ (sectorParameterEquiv 0 i) ''
            {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ∧
          C e i ∩ H e '' ((H e).source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
            H e '' ((sectorParameterEquiv 0 i) ''
              ((Icc (0 : ℝ) (r e) ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) (r e))))) ∧
        IsOpen (W e) ∧ alpha (if e then A else 0) ∈ W e ∧
        IsCompact (D e) ∧ D e ⊆ closure U ∧ W e ∩ closure U ⊆ D e ∧
        D e ∩ frontier U =
          (fun s => alpha (if e then A - s else s)) '' Icc 0 (r e) ∪
          (fun s => beta (if e then B - s else s)) '' Icc 0 (r e)) ∧
      Disjoint (D false) (D true) ∧
    ∃ rev0 : Bool,
      let g0 : ℝ → AnnulusCoordinates := fun t => alpha (if rev0 then A - t else t)
      let r0 (e : Bool) := r (if rev0 then !e else e)
      ∃ (d0 : ℝ → AnnulusCoordinates) (n0 : ℕ) (c0 : Fin (n0 + 1) → ℝ)
        (L0 : Fin n0 → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G0 : Fin n0 → OpenPartialHomeomorph ℝ ℝ) (f0 : Fin n0 → ℝ → ℝ) (ell0 : ℝ),
        0 < n0 ∧ StrictMono c0 ∧ c0 0 = r0 false ∧ c0 (Fin.last n0) = A - r0 true ∧ 0 < ell0 ∧
        ∃ B0 : ∀ i : Fin n0,
          ObliqueBandFaces
            (collarParameterEquiv.trans (L0 i).symm).toHomeomorph.toOpenPartialHomeomorph
            (f0 i) (G0 i (c0 i.castSucc)) (G0 i (c0 i.succ))
            (L0 i (d0 (c0 i.castSucc))).1 (L0 i (d0 (c0 i.castSucc))).2
            (L0 i (d0 (c0 i.succ))).1 (L0 i (d0 (c0 i.succ))).2 ell0 ell0,
          (∀ i, (B0 i).lowerArc = g0 '' Icc (c0 i.castSucc) (c0 i.succ) ∧
            (B0 i).leftCut = segment ℝ (g0 (c0 i.castSucc))
              (g0 (c0 i.castSucc) + ell0 • d0 (c0 i.castSucc)) ∧
            (B0 i).rightCut = segment ℝ (g0 (c0 i.succ))
              (g0 (c0 i.succ) + ell0 • d0 (c0 i.succ)) ∧
            (B0 i).carrier ⊆ closure U ∧ (B0 i).carrier \ (B0 i).lowerArc ⊆ U) ∧
          (∀ i j : Fin n0, i.succ < j.castSucc → Disjoint (B0 i).carrier (B0 j).carrier) ∧
          (∀ i j : Fin n0, i.succ = j.castSucc →
            (B0 i).carrier ∩ (B0 j).carrier = segment ℝ (g0 (c0 i.succ))
              (g0 (c0 i.succ) + ell0 • d0 (c0 i.succ))) ∧
          (∀ i, (D false ∪ D true) ∩ (B0 i).carrier =
            (if c0 i.castSucc = r0 false then (B0 i).leftCut else ∅) ∪
              (if c0 i.succ = A - r0 true then (B0 i).rightCut else ∅)) ∧
          (∀ p ∈ Icc (0 : ℝ) A, ∃ W : Set AnnulusCoordinates,
            IsOpen W ∧ g0 p ∈ W ∧
              W ∩ closure U ⊆ (D false ∪ D true) ∪ ⋃ i, (B0 i).carrier) ∧
    ∃ rev1 : Bool,
      let g1 : ℝ → AnnulusCoordinates := fun t => beta (if rev1 then B - t else t)
      let r1 (e : Bool) := r (if rev1 then !e else e)
      ∃ (d1 : ℝ → AnnulusCoordinates) (n1 : ℕ) (c1 : Fin (n1 + 1) → ℝ)
        (L1 : Fin n1 → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G1 : Fin n1 → OpenPartialHomeomorph ℝ ℝ) (f1 : Fin n1 → ℝ → ℝ) (ell1 : ℝ),
        0 < n1 ∧ StrictMono c1 ∧ c1 0 = r1 false ∧ c1 (Fin.last n1) = B - r1 true ∧ 0 < ell1 ∧
        ∃ B1 : ∀ i : Fin n1,
          ObliqueBandFaces
            (collarParameterEquiv.trans (L1 i).symm).toHomeomorph.toOpenPartialHomeomorph
            (f1 i) (G1 i (c1 i.castSucc)) (G1 i (c1 i.succ))
            (L1 i (d1 (c1 i.castSucc))).1 (L1 i (d1 (c1 i.castSucc))).2
            (L1 i (d1 (c1 i.succ))).1 (L1 i (d1 (c1 i.succ))).2 ell1 ell1,
          (∀ i, (B1 i).lowerArc = g1 '' Icc (c1 i.castSucc) (c1 i.succ) ∧
            (B1 i).leftCut = segment ℝ (g1 (c1 i.castSucc))
              (g1 (c1 i.castSucc) + ell1 • d1 (c1 i.castSucc)) ∧
            (B1 i).rightCut = segment ℝ (g1 (c1 i.succ))
              (g1 (c1 i.succ) + ell1 • d1 (c1 i.succ)) ∧
            (B1 i).carrier ⊆ closure U ∧ (B1 i).carrier \ (B1 i).lowerArc ⊆ U) ∧
          (∀ i j : Fin n1, i.succ < j.castSucc → Disjoint (B1 i).carrier (B1 j).carrier) ∧
          (∀ i j : Fin n1, i.succ = j.castSucc →
            (B1 i).carrier ∩ (B1 j).carrier = segment ℝ (g1 (c1 i.succ))
              (g1 (c1 i.succ) + ell1 • d1 (c1 i.succ))) ∧
          (∀ i, (D false ∪ D true) ∩ (B1 i).carrier =
            (if c1 i.castSucc = r1 false then (B1 i).leftCut else ∅) ∪
              (if c1 i.succ = B - r1 true then (B1 i).rightCut else ∅)) ∧
          (∀ p ∈ Icc (0 : ℝ) B, ∃ W : Set AnnulusCoordinates,
            IsOpen W ∧ g1 p ∈ W ∧
              W ∩ closure U ⊆ (D false ∪ D true) ∪ ⋃ i, (B1 i).carrier)
          ∧ (∀ i j, Disjoint (B0 i).carrier (B1 j).carrier) ∧
          let R := ((D false ∪ D true) ∪ ⋃ i, (B0 i).carrier) ∪ ⋃ i, (B1 i).carrier
          ∃ core : TriangleMesh,
            core.toPlaneComplex.support = closure (U \ R) ∧
            closure U = R ∪ core.toPlaneComplex.support ∧
            ∀ p ∈ closure U ∩ frontier U, ∃ Q : Set AnnulusCoordinates,
              IsOpen Q ∧ p ∈ Q ∧ Q ∩ closure U ⊆ R := by
  classical
  obtain ⟨H, r, F, W, positive, hdata, hCC,
    rev0, d0, n0, c0, L0, G0, f0, ell0, hn0, hc0, hfirst0, hlast0, hell0,
    B0, hB0, hsep0, hadj0, hcap0, hcover0,
    rev1, d1, n1, c1, L1, G1, f1, ell1, hn1, hc1, hfirst1, hlast1, hell1,
    B1, hB1, hsep1, hadj1, hcap1, hcover1, hcross⟩ :=
    m64Intrinsic_exists_two_arc_covered_bands ha hb hA hB hai hbi hareg hbreg hinter
      hbase hend hind0 hind1 hU hV hdisj hfU hfV
  let D (e : Bool) := ⋃ i,
    ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)),
      F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
  let R := ((D false ∪ D true) ∪ ⋃ i, (B0 i).carrier) ∪ ⋃ i, (B1 i).carrier
  let g0 : ℝ → AnnulusCoordinates := fun t => alpha (if rev0 then A - t else t)
  let g1 : ℝ → AnnulusCoordinates := fun t => beta (if rev1 then B - t else t)
  have hr (e : Bool) := (hdata e).1
  have hrbound (e : Bool) := (hdata e).2.1
  have hax0 (e : Bool) := (hdata e).2.2.2.2.2.2.1
  have hax1 (e : Bool) := (hdata e).2.2.2.2.2.2.2.1
  have hFdata (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.2.2.2.1
  have hCcompact (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsub (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrA (e : Bool) : r e ≤ A := by
    have hb := (hrbound e).trans
      (div_le_div_of_nonneg_right (min_le_left A B) (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hrB (e : Bool) : r e ≤ B := by
    have hb := (hrbound e).trans
      (div_le_div_of_nonneg_right (min_le_right A B) (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have himage0 : g0 '' Icc 0 A = alpha '' Icc 0 A := by
    cases rev0
    · rfl
    · change (alpha ∘ fun t => A - t) '' Icc 0 A = _
      rw [image_comp, image_const_sub_Icc]
      simp only [sub_self, sub_zero]
  have himage1 : g1 '' Icc 0 B = beta '' Icc 0 B := by
    cases rev1
    · rfl
    · change (beta ∘ fun t => B - t) '' Icc 0 B = _
      rw [image_comp, image_const_sub_Icc]
      simp only [sub_self, sub_zero]
  have hcut0 (k : Fin (n0 + 1)) : c0 k ∈ Icc (0 : ℝ) A := by
    have hl := hc0.monotone (Fin.zero_le k)
    have hu := hc0.monotone (Fin.le_last k)
    rw [hfirst0] at hl
    rw [hlast0] at hu
    exact ⟨(hr _).le.trans hl, hu.trans (sub_le_self A (hr _).le)⟩
  have hcut1 (k : Fin (n1 + 1)) : c1 k ∈ Icc (0 : ℝ) B := by
    have hl := hc1.monotone (Fin.zero_le k)
    have hu := hc1.monotone (Fin.le_last k)
    rw [hfirst1] at hl
    rw [hlast1] at hu
    exact ⟨(hr _).le.trans hl, hu.trans (sub_le_self B (hr _).le)⟩
  have hlower0 (i : Fin n0) : (B0 i).lowerArc ⊆ frontier U := by
    have him : g0 '' Icc 0 A ⊆ frontier U := by
      rw [himage0, hfU]
      exact subset_union_left
    rw [(hB0 i).1]
    exact (image_mono (Icc_subset_Icc (hcut0 i.castSucc).1 (hcut0 i.succ).2)).trans him
  have hlower1 (i : Fin n1) : (B1 i).lowerArc ⊆ frontier U := by
    have him : g1 '' Icc 0 B ⊆ frontier U := by
      rw [himage1, hfU]
      exact subset_union_right
    rw [(hB1 i).1]
    exact (image_mono (Icc_subset_Icc (hcut1 i.castSucc).1 (hcut1 i.succ).2)).trans him
  have hlocal : ∀ p ∈ closure U ∩ frontier U, ∃ Q : Set AnnulusCoordinates,
      IsOpen Q ∧ p ∈ Q ∧ Q ∩ closure U ⊆ R := by
    intro p hp
    rw [hfU, ← himage0, ← himage1] at hp
    rcases hp.2 with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · obtain ⟨Q, hQ, hpQ, hcover⟩ := hcover0 t ht
      exact ⟨Q, hQ, hpQ, hcover.trans subset_union_left⟩
    · obtain ⟨Q, hQ, hpQ, hcover⟩ := hcover1 t ht
      exact ⟨Q, hQ, hpQ, hcover.trans
        (union_subset (fun _ hz => Or.inl (Or.inl hz)) (fun _ hz => Or.inr hz))⟩
  have hparam {T r : ℝ} (hr : 0 ≤ r) (hrT : r ≤ T)
      (e : Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (if e then T - t * r else t * r) ∈ Icc (0 : ℝ) T := by
    have ht' : t * r ∈ Icc (0 : ℝ) T :=
      ⟨mul_nonneg ht.1 hr, (mul_le_of_le_one_left hr ht.2).trans hrT⟩
    cases e
    · exact ht'
    · change T - t * r ∈ Icc (0 : ℝ) T
      constructor <;> linarith [ht'.1, ht'.2]
  have haxes (e : Bool) :
      (fun t : ℝ => H e (0, t * r e)) '' Icc 0 1 ∪
        (fun t : ℝ => H e (t * r e, 0)) '' Icc 0 1 ⊆ frontier U := by
    rintro z (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · dsimp only
      rw [hax1, hfU]
      exact Or.inr ⟨_, hparam (hr e).le (hrB e) e t ht, rfl⟩
    · dsimp only
      rw [hax0, hfU]
      exact Or.inl ⟨_, hparam (hr e).le (hrA e) e t ht, rfl⟩
  have hcaplines (e : Bool) := m64Intrinsic_retained_corner_frontier_lines
    (hr e) (H e) (F e) (positive e)
      (fun i => (hFdata e i).1) (fun i => (hFdata e i).2.2.1)
      (fun i => (hFdata e i).2.2.2.1) (fun i => (hFdata e i).2.2.2.2.1)
      (fun i => (hFdata e i).2.2.2.2.2.1)
      (fun i => (hFdata e i).2.2.2.2.2.2.1)
      (fun i => (hFdata e i).2.2.2.2.2.2.2.1) (haxes e)
  let pieces : Bool ⊕ (Fin n0 ⊕ Fin n1) → Set AnnulusCoordinates
    | .inl e => D e
    | .inr (.inl i) => (B0 i).carrier
    | .inr (.inr i) => (B1 i).carrier
  have hpieces : (⋃ i, pieces i) = R := by
    ext p
    simp only [pieces, R, mem_iUnion, Sum.exists, Bool.exists_bool, mem_union]
    tauto
  have hclosed : ∀ i, IsClosed (pieces i) := by
    rintro (e | (i | i))
    · exact (hCcompact e).isClosed
    · exact (B0 i).isClosed_carrier
    · exact (B1 i).isClosed_carrier
  have hsub' : ∀ i, pieces i ⊆ closure U := by
    rintro (e | (i | i))
    · exact hsub e
    · exact (hB0 i).2.2.2.1
    · exact (hB1 i).2.2.2.1
  have hlinefamily : ∀ i,
      ∃ lines : List (AnnulusCoordinates →ᵃ[ℝ] ℝ),
        (∀ l ∈ lines, Function.Surjective l) ∧
          frontier (pieces i) \ frontier U ⊆ ⋃ l ∈ lines, {z | l z = 0} := by
    rintro (e | (i | i))
    · obtain ⟨_, _, lines, hlines, hfront⟩ := hcaplines e
      exact ⟨lines, hlines, fun z hz => (hfront hz.1).resolve_left hz.2⟩
    · obtain ⟨lines, hlines, hfront⟩ := m64Intrinsic_linear_band_frontier_lines (L0 i).symm (B0 i)
      exact ⟨lines, hlines, fun z hz =>
        (hfront hz.1).resolve_left (fun h => hz.2 (hlower0 i h))⟩
    · obtain ⟨lines, hlines, hfront⟩ := m64Intrinsic_linear_band_frontier_lines (L1 i).symm (B1 i)
      exact ⟨lines, hlines, fun z hz =>
        (hfront hz.1).resolve_left (fun h => hz.2 (hlower1 i h))⟩
  obtain ⟨lines, hlines, hlinesub⟩ := Poincare.Topology.Plane.exists_affine_lines_iUnion
    (fun i => frontier (pieces i) \ frontier U) hlinefamily
  have hfront : ∀ i, frontier (pieces i) ⊆ frontier U ∪
      (chartAt AnnulusCoordinates (0 : AnnulusCoordinates)) ⁻¹'
        (⋃ l ∈ lines, {z | l z = 0}) := by
    intro i z hz
    by_cases htrace : z ∈ frontier U
    · exact Or.inl htrace
    · right
      simpa using hlinesub (mem_iUnion.mpr ⟨i, hz, htrace⟩)
  obtain ⟨core, hcore, _, _, _, hrecovery, _, _⟩ :=
    exists_exact_polygonal_remainder_mesh_with_refinement (0 : AnnulusCoordinates)
      hU hcompact (by intro z _; simp) pieces hclosed hsub' (Subset.refl (frontier U))
      lines hlines hfront (by simpa only [hpieces] using hlocal)
  have hcore' : core.toPlaneComplex.support = closure (U \ R) := by
    simpa only [hpieces, chartAt_self_eq, OpenPartialHomeomorph.refl_apply, image_id] using hcore
  have hrecovery' : closure U = R ∪ core.toPlaneComplex.support := by
    simpa [hpieces] using hrecovery
  exact ⟨H, r, F, W, positive, hdata, hCC,
    rev0, d0, n0, c0, L0, G0, f0, ell0, hn0, hc0, hfirst0, hlast0, hell0,
    B0, hB0, hsep0, hadj0, hcap0, hcover0,
    rev1, d1, n1, c1, L1, G1, f1, ell1, hn1, hc1, hfirst1, hlast1, hell1,
    B1, hB1, hsep1, hadj1, hcap1, hcover1, hcross, core, hcore', hrecovery', hlocal⟩

end PoincareConjecture
