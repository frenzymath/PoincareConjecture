import PoincareConjecture.Proofs.M25.Topology3D.Polygon.BoundaryBasics
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TubeCoordinates
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem exists_continuous_polygon_family_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {n : ℕ} {K : Set ℝ} (hK : IsCompact K) (p : ℝ → Polygon E n)
    (hp : ∀ i : Fin n, ContinuousOn (fun z => p z i) K)
    (P : ℝ × E → Y)
    (hP : ContinuousOn P {a | a.1 ∈ K ∧ a.2 ∈ (p a.1).boundary ℝ})
    (hbij : ∀ z ∈ K, BijOn (fun y => P (z, y)) ((p z).boundary ℝ) univ) :
    ∃ f : K × Y → E, Continuous f ∧ ∀ z : K, ∀ q : Y,
      f (z, q) ∈ (p z).boundary ℝ ∧ P (z, f (z, q)) = q ∧
        ∀ y ∈ (p z).boundary ℝ, P (z, y) = q → y = f (z, q) := by
  classical
  let D : Set (ℝ × E) := {a | a.1 ∈ K ∧ a.2 ∈ (p a.1).boundary ℝ}
  let L : Fin n → ℝ × ℝ → ℝ × E := fun i a => (a.1, (p a.1).edgePath ℝ i a.2)
  have hL : ∀ i, ContinuousOn (L i) (K ×ˢ Icc (0 : ℝ) 1) := by
    intro i
    have hleft : ContinuousOn (fun a : ℝ × ℝ => p a.1 i) (K ×ˢ Icc (0 : ℝ) 1) :=
      (hp i).comp continuous_fst.continuousOn (fun a ha => ha.1)
    have hright : ContinuousOn (fun a : ℝ × ℝ => p a.1 (finRotate n i))
        (K ×ˢ Icc (0 : ℝ) 1) :=
      (hp (finRotate n i)).comp continuous_fst.continuousOn (fun a ha => ha.1)
    exact continuous_fst.continuousOn.prodMk
      (hleft.lineMap hright continuous_snd.continuousOn)
  have hD : D = ⋃ i, L i '' (K ×ˢ Icc (0 : ℝ) 1) := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff (p a.1) a.2).mp ha.2
      obtain ⟨t, ht, heq⟩ := hi
      exact mem_iUnion.mpr ⟨i, (a.1, t), ⟨ha.1, ht⟩, Prod.ext rfl heq⟩
    · intro ha
      obtain ⟨i, b, hb, rfl⟩ := mem_iUnion.mp ha
      exact ⟨hb.1, polygon_edgeSet_subset_boundary (p b.1) i ⟨b.2, hb.2, rfl⟩⟩
  have hcompact : IsCompact D := by
    rw [hD]
    exact isCompact_iUnion (fun i => (hK.prod isCompact_Icc).image_of_continuousOn (hL i))
  let : CompactSpace D := isCompact_iff_compactSpace.mp hcompact
  let G : D → K × Y := fun a => (⟨a.1.1, a.2.1⟩, P a.1)
  have hG : Continuous G :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun a => a.2.1)).prodMk
      (hP.comp_continuous continuous_subtype_val (fun a => a.2))
  have hGbij : Bijective G := by
    constructor
    · intro a b hab
      have hz : a.1.1 = b.1.1 := congrArg (fun u : K × Y => (u.1 : ℝ)) hab
      have hval : P a.1 = P b.1 := congrArg Prod.snd hab
      apply Subtype.ext
      apply Prod.ext hz
      apply (hbij a.1.1 a.2.1).injOn a.2.2
      · simpa only [hz] using b.2.2
      · change P (a.1.1, a.1.2) = P (b.1.1, b.1.2) at hval
        simpa only [hz] using hval
    · intro u
      obtain ⟨y, hy, heq⟩ := (hbij u.1 u.1.2).surjOn (mem_univ u.2)
      exact ⟨⟨(u.1, y), u.1.2, hy⟩, Prod.ext rfl heq⟩
  let e : D ≃ K × Y := Equiv.ofBijective G hGbij
  have he : Continuous e := hG
  let H : D ≃ₜ K × Y := he.homeoOfEquivCompactToT2
  let f : K × Y → E := fun u => (H.symm u).1.2
  refine ⟨f, (continuous_subtype_val.comp H.symm.continuous).snd, ?_⟩
  intro z q
  have hid : G (H.symm (z, q)) = (z, q) := H.apply_symm_apply (z, q)
  have hz : (H.symm (z, q)).1.1 = (z : ℝ) :=
    congrArg (fun u : K × Y => (u.1 : ℝ)) hid
  have hmem : f (z, q) ∈ (p z).boundary ℝ := by
    simpa only [hz] using (H.symm (z, q)).2.2
  have hval : P (z, f (z, q)) = q := by
    have h := congrArg Prod.snd hid
    change P ((H.symm (z, q)).1.1, f (z, q)) = q at h
    simpa only [hz] using h
  refine ⟨hmem, hval, ?_⟩
  intro y hy hq
  exact (hbij z z.2).injOn hy hmem (hq.trans hval.symm)

theorem exists_continuous_polygon_family_normal_graph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
    (c : ℝ → sphere (0 : E) 1 → E)
    (T : OpenPartialHomeomorph (ℝ × E) (ℝ × E))
    {l u w : ℝ} (hw : w < 1)
    (hs : T.source = Ioo l u ×ˢ {x : E | |‖x‖ - 1| < w})
    (he : ∀ a : ℝ × E, T a = (a.1, curveAnnularExtension o q0 c a))
    (hInv : ContDiffOn ℝ ∞ T.symm T.target)
    {n : ℕ} {K : Set ℝ} (hK : IsCompact K) (p : ℝ → Polygon E n)
    (hp : ∀ i : Fin n, ContinuousOn (fun z => p z i) K)
    (htarget : ∀ z ∈ K, ∀ y ∈ (p z).boundary ℝ, (z, y) ∈ T.target)
    (hbij : ∀ z ∈ K, BijOn (fun y => curveTubeProjection q0 T (z, y))
      ((p z).boundary ℝ) univ) :
    ∃ h : K × sphere (0 : E) 1 → ℝ, Continuous h ∧ ∀ z : K,
      (∀ q, |h (z, q)| < w) ∧
      (p z).boundary ℝ = range (fun q => c z q + h (z, q) •
        curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))) ∧
      ∀ q,
        let y := c z q + h (z, q) •
          curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))
        curveTubeProjection q0 T (z, y) = q ∧ curveTubeHeight T (z, y) = h (z, q) := by
  let D : Set (ℝ × E) := {a | a.1 ∈ K ∧ a.2 ∈ (p a.1).boundary ℝ}
  have hx : ∀ a ∈ T.target, (T.symm a).2 ≠ 0 :=
    fun a ha => (curveAnnularTube_coordinates o q0 c T hw hs he ha).1
  have hP : ContinuousOn (curveTubeProjection q0 T) D :=
    (contMDiffOn_curveTubeProjection (n := 1) q0 T hInv hx).continuousOn.mono
      (fun a ha => htarget a.1 ha.1 a.2 ha.2)
  obtain ⟨f, hf, hfi⟩ := exists_continuous_polygon_family_inverse hK p hp
    (curveTubeProjection q0 T) hP hbij
  let F : K × sphere (0 : E) 1 → ℝ × E := fun a => (a.1, f a)
  have hF : Continuous F := (continuous_subtype_val.comp continuous_fst).prodMk hf
  have hFt : ∀ a, F a ∈ T.target := fun a =>
    htarget a.1 a.1.2 (f a) (hfi a.1 a.2).1
  let h : K × sphere (0 : E) 1 → ℝ := fun a => curveTubeHeight T (F a)
  have hh : Continuous h :=
    (contDiffOn_curveTubeHeight T hInv hx).continuousOn.comp_continuous hF hFt
  have hgraph : ∀ z : K, ∀ q, f (z, q) = c z q + h (z, q) •
      curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E)) := by
    intro z q
    have hcoord := (curveAnnularTube_coordinates o q0 c T hw hs he (hFt (z, q))).2.2.2.2
    change f (z, q) = c z (curveTubeProjection q0 T (z, f (z, q))) +
      h (z, q) • curveFamilyNormal o (radialFamilyExtension q0 c)
        (z, (curveTubeProjection q0 T (z, f (z, q)) : E)) at hcoord
    simpa only [(hfi z q).2.1] using hcoord
  refine ⟨h, hh, ?_⟩
  intro z
  refine ⟨fun q => (curveAnnularTube_coordinates o q0 c T hw hs he (hFt (z, q))).2.2.1,
    ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      let q := curveTubeProjection q0 T (z, y)
      have hyf := (hfi z q).2.2 y hy rfl
      exact ⟨q, (hgraph z q).symm.trans hyf.symm⟩
    · rintro ⟨q, rfl⟩
      dsimp only
      rw [← hgraph z q]
      exact (hfi z q).1
  · intro q
    dsimp only
    rw [← hgraph z q]
    exact ⟨(hfi z q).2.1, rfl⟩

end PoincareConjecture.M25.Topology3D
