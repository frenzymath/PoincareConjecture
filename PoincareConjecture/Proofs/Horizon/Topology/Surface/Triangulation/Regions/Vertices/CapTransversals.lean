import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.CapAvoidance
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.TransverseDirections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology Manifold
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface

private theorem graph_transverse_ne_zero_of_separator
    {d : ℝ × ℝ} {h' : ℝ} (hd : d ≠ 0)
    (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (hℓ : ℓ (1, h') ≠ 0) (hker : ℓ d = 0) :
    d.2 - h' * d.1 ≠ 0 := by
  intro he
  have hdline : d = d.1 • ((1 : ℝ), h') := by
    ext <;> simp only [Prod.smul_mk, smul_eq_mul, mul_one]
    linarith
  have hmul : d.1 * ℓ (1, h') = 0 := by
    rw [← smul_eq_mul, ← map_smul, ← hdline]
    exact hker
  have hd1 : d.1 = 0 := (mul_eq_zero.mp hmul).resolve_right hℓ
  apply hd
  rw [hdline, hd1, zero_smul]

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {r : M → ℝ} {p : M} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → M} (B : VertexCapFaces P x)

noncomputable def chordEndpoint (s : Bool × Bool) (vertical : Bool) :
    EuclideanSpace ℝ (Fin 2) :=
  if vertical then B.planarCoordinates s (0, B.scale)
  else B.planarCoordinates s (B.scale, 0)

noncomputable def chordDirection (s : Bool × Bool) (vertical : Bool) :
    EuclideanSpace ℝ (Fin 2) :=
  if vertical then B.planarCoordinates s (B.scale, 0) - B.planarCoordinates s (0, B.scale)
  else B.planarCoordinates s (0, B.scale) - B.planarCoordinates s (B.scale, 0)

omit [T2Space M] in
theorem chordEndpoint_eq_chart_radial (s : Bool × Bool) (vertical : Bool) :
    B.chordEndpoint s vertical = chartAt (EuclideanSpace ℝ (Fin 2)) (x s)
      (P.sectorCoordinates s (if vertical then (0, B.scale) else (B.scale, 0))) := by
  cases vertical
  · exact B.planar_first s B.scale ⟨B.scale_pos.le, le_rfl⟩
  · exact B.planar_second s B.scale ⟨B.scale_pos.le, le_rfl⟩

omit [T2Space M] in
theorem chordDirection_ne_zero (s : Bool × Bool) (vertical : Bool) :
    B.chordDirection s vertical ≠ 0 := by
  have hfirst : (B.scale, (0 : ℝ)) ∈ (B.planarCoordinates s).source :=
    B.planar_source s ⟨B.scale_pos.le, le_rfl, by simp⟩
  have hsecond : ((0 : ℝ), B.scale) ∈ (B.planarCoordinates s).source :=
    B.planar_source s ⟨le_rfl, B.scale_pos.le, by simp⟩
  have hne : B.planarCoordinates s (B.scale, 0) ≠ B.planarCoordinates s (0, B.scale) := by
    intro he
    exact B.scale_pos.ne' (congrArg Prod.fst ((B.planarCoordinates s).injOn hfirst hsecond he))
  cases vertical
  · exact sub_ne_zero.mpr hne.symm
  · exact sub_ne_zero.mpr hne

omit [T2Space M] in
theorem chord_ray_eq_affine (s : Bool × Bool) (vertical : Bool) (t : ℝ) :
    B.chordEndpoint s vertical + t • B.chordDirection s vertical =
      (1 - (if vertical then 1 - t else t)) • B.planarCoordinates s (B.scale, 0) +
        (if vertical then 1 - t else t) • B.planarCoordinates s (0, B.scale) := by
  cases vertical <;> dsimp [chordEndpoint, chordDirection] <;> module

omit [T2Space M] in
theorem chord_ray_eq_boundary (s : Bool × Bool) (vertical : Bool) (t : ℝ) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) (x s)).symm
      (B.chordEndpoint s vertical + t • B.chordDirection s vertical) =
        ((B.face s).boundary 0).map (if vertical then 1 - t else t) := by
  rw [B.chord_map, B.chord_ray_eq_affine]
  rw [B.planar_first s B.scale ⟨B.scale_pos.le, le_rfl⟩,
    B.planar_second s B.scale ⟨B.scale_pos.le, le_rfl⟩]

omit [T2Space M] in
theorem chord_ray_mem_target (s : Bool × Bool) (vertical : Bool)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    B.chordEndpoint s vertical + t • B.chordDirection s vertical ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x s)).target := by
  let a := if vertical then 1 - t else t
  have ha : a ∈ Icc (0 : ℝ) 1 := by cases vertical <;> dsimp [a] <;> constructor <;> linarith [ht.1, ht.2]
  rw [B.chord_ray_eq_affine, ← B.planar_chord]
  exact B.planar_target s ((B.planarCoordinates s).map_source (B.planar_source s
    ⟨mul_nonneg (sub_nonneg.mpr ha.2) B.scale_pos.le,
      mul_nonneg ha.1 B.scale_pos.le, by dsimp [a] at *; nlinarith⟩))

omit [T2Space M] in

theorem chord_ray_mem_sector (s : Bool × Bool) (vertical : Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) (x s)).symm
      (B.chordEndpoint s vertical + t • B.chordDirection s vertical) ∈ P.sector s := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) (x s)
  let F := B.planarCoordinates s
  let a := if vertical then 1 - t else t
  let q : ℝ × ℝ := ((1 - a) * B.scale, a * B.scale)
  have ha : a ∈ Ioo (0 : ℝ) 1 := by cases vertical <;> dsimp [a] <;> constructor <;> linarith [ht.1, ht.2]
  have hq : 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ B.scale := by
    dsimp [q]
    exact ⟨(mul_pos (sub_pos.mpr ha.2) B.scale_pos).le,
      (mul_pos ha.1 B.scale_pos).le, by nlinarith⟩
  have hqsource : q ∈ F.source := B.planar_source s hq
  have hqtarget : F q ∈ c.target := B.planar_target s (F.map_source hqsource)
  have hqcap : c.symm (F q) ∈ (B.face s).carrier := by
    rw [B.carrier_planar]
    exact ⟨F q, ⟨q, hq, rfl⟩, rfl⟩
  have heq : B.chordEndpoint s vertical + t • B.chordDirection s vertical = F q := by
    rw [B.chord_ray_eq_affine, ← B.planar_chord]
  rw [heq]
  rcases B.carrier_subset_sector_sides s hqcap with hsector | hfirst | hsecond
  · exact hsector
  · obtain ⟨u, hu, he⟩ := hfirst
    change P.sectorCoordinates s (u, 0) = c.symm (F q) at he
    have haxis : (u, (0 : ℝ)) ∈ F.source := B.planar_source s ⟨hu.1, le_rfl, by simpa using hu.2⟩
    have hcoord : F (u, 0) = F q := by
      rw [B.planar_first s u hu, he]
      exact c.right_inv hqtarget
    have hzero := congrArg Prod.snd (F.injOn haxis hqsource hcoord)
    exact False.elim ((mul_pos ha.1 B.scale_pos).ne' hzero.symm)
  · obtain ⟨u, hu, he⟩ := hsecond
    change P.sectorCoordinates s (0, u) = c.symm (F q) at he
    have haxis : ((0 : ℝ), u) ∈ F.source := B.planar_source s ⟨le_rfl, hu.1, by simpa using hu.2⟩
    have hcoord : F (0, u) = F q := by
      rw [B.planar_second s u hu, he]
      exact c.right_inv hqtarget
    have hzero := congrArg Prod.fst (F.injOn haxis hqsource hcoord)
    exact False.elim ((mul_pos (sub_pos.mpr ha.2) B.scale_pos).ne' hzero.symm)

omit [T2Space M] in
theorem chord_ray_image (s : Bool × Bool) (vertical : Bool) :
    (fun t : ℝ => (chartAt (EuclideanSpace ℝ (Fin 2)) (x s)).symm
      (B.chordEndpoint s vertical + t • B.chordDirection s vertical)) '' Icc (0 : ℝ) 1 =
        ((B.face s).boundary 0).map '' Icc (0 : ℝ) 1 := by
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨if vertical then 1 - t else t, ?_, (B.chord_ray_eq_boundary s vertical t).symm⟩
    cases vertical <;> dsimp <;> constructor <;> linarith [ht.1, ht.2]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨if vertical then 1 - t else t, ?_, ?_⟩
    · cases vertical <;> dsimp <;> constructor <;> linarith [ht.1, ht.2]
    · dsimp only
      rw [B.chord_ray_eq_boundary]
      cases vertical <;> simp

omit [T2Space M] in

theorem chord_transverse_pos_of_region_tube
    (s : Bool × Bool) (vertical : Bool) {S : Set M} (hsector : P.sector s ⊆ S)
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    {h : ℝ → ℝ} {a α β δ : ℝ}
    (ha : a ∈ Ioo α β) (hδ : 0 < δ) (hh : DifferentiableAt ℝ h a)
    (hbase : A (B.chordEndpoint s vertical) = (a, h a))
    (htube : ∀ y ∈ Ioo α β, ∀ z : ℝ, |z| < δ →
      ((chartAt (EuclideanSpace ℝ (Fin 2)) (x s)).symm (A.symm (y, h y + z)) ∈ S ↔ 0 < z))
    (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (hℓ : ℓ (1, deriv h a) ≠ 0)
    (hker : ℓ (A (B.chordDirection s vertical)) = 0) :
    0 < (A (B.chordDirection s vertical)).2 -
      deriv h a * (A (B.chordDirection s vertical)).1 := by
  let p := B.chordEndpoint s vertical
  let d := B.chordDirection s vertical
  have hd : A d ≠ 0 := fun he => B.chordDirection_ne_zero s vertical
    (A.injective (he.trans A.map_zero.symm))
  have hnonzero := graph_transverse_ne_zero_of_separator hd ℓ hℓ hker
  let y : ℝ → ℝ := fun r => (A (p + r • d)).1
  let z : ℝ → ℝ := fun r => (A (p + r • d)).2 - h (y r)
  have hy : ContinuousAt y 0 := by dsimp [y]; fun_prop
  have hyzero : y 0 = a := by simpa [y] using congrArg Prod.fst hbase
  have hz : ContinuousAt z 0 := by
    have hhc : ContinuousAt h (y 0) := hyzero.symm ▸ hh.continuousAt
    exact (by fun_prop : ContinuousAt (fun r : ℝ => (A (p + r • d)).2) 0).sub
      (hhc.comp (f := y) hy)
  have hzzero : z 0 = 0 := by simp only [z, y, zero_smul, add_zero]; rw [hbase]; simp
  have hyin : ∀ᶠ r in 𝓝 (0 : ℝ), y r ∈ Ioo α β :=
    hy.preimage_mem_nhds (isOpen_Ioo.mem_nhds (hyzero.symm ▸ ha))
  have hzin : ∀ᶠ r in 𝓝 (0 : ℝ), z r ∈ Ioo (-δ) δ :=
    hz.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by rw [hzzero]; exact ⟨by linarith, hδ⟩))
  have hpolar (r : ℝ) : p + r • d = A.symm (y r, h (y r) + z r) := by
    apply A.injective
    rw [A.apply_symm_apply]
    apply Prod.ext
    · rfl
    · dsimp [z]
      ring
  have hbelow : ∀ᶠ r in 𝓝 (0 : ℝ), r < 1 := Iio_mem_nhds (by norm_num)
  have hside : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < z r := by
    filter_upwards [hyin.filter_mono nhdsWithin_le_nhds,
      hzin.filter_mono nhdsWithin_le_nhds,
      hbelow.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hyr hzr hr1 hr0
    apply (htube (y r) hyr (z r) (abs_lt.mpr hzr)).mp
    rw [← hpolar]
    exact hsector (B.chord_ray_mem_sector s vertical ⟨hr0, hr1⟩)
  have hAv : A (A.symm (1, deriv h a)) = (1 : ℝ) • ((1 : ℝ), deriv h a) := by simp
  have hAv' : A (A.symm (1, deriv h a)) = (1 : ℝ) •
      ((1 : ℝ), deriv h (A p).1) := by rw [hbase]; exact hAv
  have hhp : DifferentiableAt ℝ h (A p).1 := by rw [hbase]; exact hh
  have hp : (A p).2 = h (A p).1 := by rw [hbase]
  have h := graph_transverse_pos_of_eventually_above A A one_ne_zero hAv hAv'
    hnonzero hhp hp hside
  have hp1 : (A p).1 = a := congrArg Prod.fst hbase
  rw [hp1] at h
  exact h

omit [T2Space M] in

theorem exists_chord_ray_length
    (s : Bool × Bool) (vertical : Bool)
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    {h : ℝ → ℝ} {a α β δ : ℝ}
    (ha : a ∈ Ioo α β) (hδ : 0 < δ) (hh : ContinuousAt h a)
    (hbase : A (B.chordEndpoint s vertical) = (a, h a)) :
    ∃ ρ ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) ρ,
      (A (B.chordEndpoint s vertical + t • B.chordDirection s vertical)).1 ∈ Ioo α β ∧
      |(A (B.chordEndpoint s vertical + t • B.chordDirection s vertical)).2 -
        h (A (B.chordEndpoint s vertical + t • B.chordDirection s vertical)).1| < δ := by
  let y : ℝ → ℝ := fun t => (A (B.chordEndpoint s vertical + t • B.chordDirection s vertical)).1
  let z : ℝ → ℝ := fun t => (A (B.chordEndpoint s vertical + t • B.chordDirection s vertical)).2 - h (y t)
  have hy : ContinuousAt y 0 := by dsimp [y]; fun_prop
  have hyzero : y 0 = a := by simpa [y] using congrArg Prod.fst hbase
  have hz : ContinuousAt z 0 := by
    have hhc : ContinuousAt h (y 0) := hyzero.symm ▸ hh
    exact (by fun_prop : ContinuousAt
      (fun t : ℝ => (A (B.chordEndpoint s vertical + t • B.chordDirection s vertical)).2) 0).sub
        (hhc.comp (f := y) hy)
  have hzzero : z 0 = 0 := by simp only [z, y, zero_smul, add_zero]; rw [hbase]; simp
  have hyin : ∀ᶠ t in 𝓝 (0 : ℝ), y t ∈ Ioo α β :=
    hy.preimage_mem_nhds (isOpen_Ioo.mem_nhds (hyzero.symm ▸ ha))
  have hzin : ∀ᶠ t in 𝓝 (0 : ℝ), z t ∈ Ioo (-δ) δ :=
    hz.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by rw [hzzero]; exact ⟨by linarith, hδ⟩))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hyin.and hzin)
  let ρ := min (ε / 2) (1 / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hρε : ρ < ε := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨ρ, ⟨hρ, (min_le_right _ _).trans_lt (by norm_num)⟩, ?_⟩
  intro t ht
  have htb : t ∈ Metric.ball (0 : ℝ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1] using
      ht.2.trans_lt hρε
  exact ⟨(hball htb).1, abs_lt.mpr (hball htb).2⟩

end ChartCircleArrangementVertexPatch.VertexCapFaces

namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

theorem exists_incident_cap_chord_transversal
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : M))
    (region : D.vertices → Bool × Bool → D.regions) (chart : D.regions → M)
    (B : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
      (fun s => chart (region p s)))
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier)
    (hsector : ∀ p i, (P p).sector i ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i))
    (hclosed : ∀ p i, (P p).closedSector i ⊆ closure (connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ (region p i)))
    (p : D.vertices) (e : D.EdgeIndex) (terminal : Bool) {cut : ℝ}
    (hcut : cut ∈ Ioo (0 : ℝ) 1) {i j : Bool × Bool} (hij : i ≠ j)
    (k : Fin 3) (hk : k = 1 ∨ k = 2)
    (hend : ∀ s, s = i ∨ s = j →
      (((B p).face s).boundary k).map 1 = D.edgeFromEndpoint e terminal cut)
    (hparameters : ∀ s, s = i ∨ s = j → ∃ J : OpenPartialHomeomorph ℝ ℝ,
      J (B p).scale = cut ∧ Icc 0 (B p).scale ⊆ J.source ∧
      StrictMonoOn J J.source ∧ ContDiffOn ℝ ∞ J J.source ∧
      ∀ u ∈ Icc 0 (B p).scale, D.edgeFromEndpoint e terminal (J u) =
        (P p).sectorCoordinates s (if k = 1 then (0, u) else (u, 0)))
    (R : D.regions) (hR : R = D.regionLeft e ∨ R = D.regionRight e)
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) {h : ℝ → ℝ}
    (hG : ContDiffOn ℝ ∞ G G.source) (hh : ContDiffOn ℝ ∞ h G.target)
    (hsource : G.source ⊆ (D.edge e.1 e.2).map ⁻¹'
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).source)
    (hgraph : ∀ t ∈ G.source,
      A (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ((D.edge e.1 e.2).map t)) =
        (G t, h (G t)))
    (ht : (if terminal then 1 - cut else cut) ∈ G.source)
    (hprojection : 0 < (A (deriv
      (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R) ∘ (D.edge e.1 e.2).map)
        (if terminal then 1 - cut else cut))).1)
    {α β δ : ℝ} (htube_base : G (if terminal then 1 - cut else cut) ∈ Ioo α β)
    (hδ : 0 < δ)
    (htube : ∀ y ∈ Ioo α β, ∀ z : ℝ, |z| < δ →
      ((chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)).symm (A.symm (y, h y + z)) ∈
        connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R ↔ 0 < z)) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)
    let t := if terminal then 1 - cut else cut
    ∃ (s : Bool × Bool) (d : EuclideanSpace ℝ (Fin 2))
      (ℓ : (ℝ × ℝ) →L[ℝ] ℝ) (W : Set (ℝ × ℝ)) (ρ : ℝ),
      (s = i ∨ s = j) ∧ region p s = R ∧
      d = (B p).chordDirection s (decide (k = 1)) ∧ d ≠ 0 ∧
      (B p).chordEndpoint s (decide (k = 1)) = c (D.edgeFromEndpoint e terminal cut) ∧
      0 < (A d).2 - deriv h (G t) * (A d).1 ∧
      ℓ (A d) = 0 ∧
      (if terminal then ℓ (1, deriv h (G t)) < 0 else 0 < ℓ (1, deriv h (G t))) ∧
      IsOpen W ∧ (G t, h (G t)) ∈ W ∧
      (∀ q ∈ D.graphCapObstacle region chart B R A ∩ W,
        ℓ (q - (G t, h (G t))) ≤ 0) ∧
      ρ ∈ Ioo (0 : ℝ) 1 ∧
      (∀ u : ℝ, c.symm (c (D.edgeFromEndpoint e terminal cut) + u • d) =
        (((B p).face s).boundary 0).map (if k = 1 then 1 - u else u)) ∧
      (fun u : ℝ => c.symm (c (D.edgeFromEndpoint e terminal cut) + u • d)) '' Icc (0 : ℝ) 1 =
        (((B p).face s).boundary 0).map '' Icc (0 : ℝ) 1 ∧
      ∀ u ∈ Icc (0 : ℝ) ρ,
        c (D.edgeFromEndpoint e terminal cut) + u • d ∈ c.target ∧
        (A (c (D.edgeFromEndpoint e terminal cut) + u • d)).1 ∈ Ioo α β ∧
        |(A (c (D.edgeFromEndpoint e terminal cut) + u • d)).2 -
          h (A (c (D.edgeFromEndpoint e terminal cut) + u • d)).1| < δ ∧
        (0 < u → c.symm (c (D.edgeFromEndpoint e terminal cut) + u • d) ∈
          connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) (chart R)
  let t := if terminal then 1 - cut else cut
  let vertical := decide (k = 1)
  obtain ⟨s, ℓ, W, hs, hsR, hW, hbaseW, hsign, hkernel, _, hsep⟩ :=
    D.exists_incident_graph_cap_separator region chart B R A hdisjoint hsector hclosed
      p e terminal hcut hij k hk hend hparameters hR G hG hh hsource hgraph ht hprojection
  let d := (B p).chordDirection s vertical
  have hradial : D.edgeFromEndpoint e terminal cut =
      (P p).sectorCoordinates s (if k = 1 then (0, (B p).scale) else ((B p).scale, 0)) := by
    obtain ⟨J, hJ, _, _, _, hcurve⟩ := hparameters s hs
    rw [← hJ]
    exact hcurve _ ⟨(B p).scale_pos.le, le_rfl⟩
  have hbase : (B p).chordEndpoint s vertical = c (D.edgeFromEndpoint e terminal cut) := by
    rw [(B p).chordEndpoint_eq_chart_radial, hradial]
    simp only [vertical, decide_eq_true_eq, hsR, c]
  have hbaseA : A ((B p).chordEndpoint s vertical) = (G t, h (G t)) := by
    rw [hbase]
    cases terminal <;> exact hgraph _ ht
  have hker : ℓ (A d) = 0 := by
    by_cases hk1 : k = 1
    · have hd : d = -((B p).planarCoordinates s (0, (B p).scale) -
          (B p).planarCoordinates s ((B p).scale, 0)) := by
        dsimp [d, ChartCircleArrangementVertexPatch.VertexCapFaces.chordDirection, vertical]
        simp only [hk1, decide_true, ite_true]
        module
      rw [hd, map_neg, map_neg, hkernel, neg_zero]
    · simpa only [d, ChartCircleArrangementVertexPatch.VertexCapFaces.chordDirection,
        vertical, hk1, decide_false, Bool.false_eq_true, ite_false] using hkernel
  have hℓ : ℓ (1, deriv h (G t)) ≠ 0 := by
    cases terminal
    · exact ne_of_gt hsign
    · exact ne_of_lt hsign
  have hhd : DifferentiableAt ℝ h (G t) :=
    ((hh _ (G.map_source ht)).contDiffAt
      (G.open_target.mem_nhds (G.map_source ht))).differentiableAt (by simp)
  have hsector' : (P p).sector s ⊆ connectedComponentIn
      (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
    simpa only [hsR] using hsector p s
  have htube' : ∀ y ∈ Ioo α β, ∀ z : ℝ, |z| < δ →
      ((chartAt (EuclideanSpace ℝ (Fin 2)) (chart (region p s))).symm (A.symm (y, h y + z)) ∈
        connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R ↔ 0 < z) := by
    simpa only [hsR] using htube
  have hpositive := (B p).chord_transverse_pos_of_region_tube s vertical hsector'
    A htube_base hδ hhd hbaseA htube' ℓ hℓ hker
  obtain ⟨ρ, hρ, hlength⟩ := (B p).exists_chord_ray_length s vertical A
    htube_base hδ hhd.continuousAt hbaseA
  refine ⟨s, d, ℓ, W, ρ, hs, hsR, rfl, (B p).chordDirection_ne_zero s vertical,
    hbase, hpositive, hker, hsign, hW, hbaseW, hsep, hρ, ?_, ?_, ?_⟩
  · intro u
    have he := (B p).chord_ray_eq_boundary s vertical u
    simpa only [hsR, hbase, vertical, decide_eq_true_eq] using he
  · have he := (B p).chord_ray_image s vertical
    simpa only [hsR, hbase] using he
  · intro u hu
    have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hρ.2.le⟩
    have htarget := (B p).chord_ray_mem_target s vertical hu1
    have hbounds := hlength u hu
    simp only [hsR, hbase] at htarget hbounds
    refine ⟨htarget, hbounds.1, hbounds.2, ?_⟩
    intro hu0
    have hregion := hsector' ((B p).chord_ray_mem_sector s vertical
      ⟨hu0, hu.2.trans_lt hρ.2⟩)
    simpa only [hsR, hbase] using hregion

end FiniteChartRegionDecomposition

end PoincareConjecture.Topology.Surface
