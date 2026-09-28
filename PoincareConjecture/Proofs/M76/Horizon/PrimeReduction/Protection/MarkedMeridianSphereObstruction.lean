import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedArcSphereObstruction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.MarkedProductInteriorChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.OriginalSphere
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalDiskProtectedBallProduct

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Square" => Set.prod (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1)
local notation "Cube" => Set.prod Square (Icc (-1 : ℝ) 1)
local notation "OpenCube" => Set.prod (Set.prod (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1)) (Ioo (-1 : ℝ) 1)

theorem ChartwisePLSphere.no_single_meridian_in_protected_product
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D S : Set (LatticeHandleAmbient ι κ L)} (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ interior (latticeHandleDomain ι κ L))
    (p : P3 → LatticeHandleAmbient ι κ L)
    (hp : PolyhedralPLInCharts e p Cube) (hpi : InjOn p Cube)
    (himage : p '' Cube = D)
    (hboundary : ∀ z ∈ Cube, p z ∈ frontier D ↔ z ∈ frontier Cube)
    (hend : ∀ side : Bool, p ((0, 0), if side then 1 else -1) ∈
      frontier (latticeHandleDomain ι κ L))
    (hmeridian : S ∩ D = p '' (Square ×ˢ {(0 : ℝ)})) : False := by
  obtain ⟨Q, hQs, hQt, hQinv, _⟩ := exists_marked_product_interior_chart
    he.compatible p hp hpi himage hboundary
  let a := markedProductCoordinates
  let T := Q.trans a.toHomeomorph.toOpenPartialHomeomorph
  have hTs : T.source = interior D := by
    simp only [T, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ, hQs]
  have hTval (x) : T x = a (Q x) := rfl
  have hTtarget (z : P3) (hz : z ∈ OpenCube) : z ∈ T.target := by
    change z ∈ univ ∩ a.symm ⁻¹' Q.target
    refine ⟨mem_univ _, ?_⟩
    rw [hQt]
    change a (a.symm z) ∈ OpenCube
    simpa only [a.apply_symm_apply] using hz
  have hTinv (z : P3) : T.symm z = p z := by
    change Q.symm (a.symm z) = p z
    rw [hQinv, a.apply_symm_apply]
  have hpT (z : P3) (hz : z ∈ OpenCube) :
      p z ∈ T.source ∧ T (p z) = z := by
    have ht := hTtarget z hz
    rw [← hTinv]
    exact ⟨T.map_target ht, T.right_inv ht⟩
  have hopenclosed : OpenCube ⊆ Cube := by
    rintro z ⟨⟨h0, h1⟩, h2⟩
    exact ⟨⟨⟨h0.1.le, h0.2.le⟩, ⟨h1.1.le, h1.2.le⟩⟩, ⟨h2.1.le, h2.2.le⟩⟩
  have hmer (z : P3) (hz : z ∈ Cube) : p z ∈ S ↔ z.2 = 0 := by
    have hpD : p z ∈ D := himage.subset ⟨z, hz, rfl⟩
    constructor
    · intro hS
      obtain ⟨w, hw, hwz⟩ := hmeridian.subset ⟨hS, hpD⟩
      have hwcube : w ∈ Cube := ⟨hw.1, by rw [show w.2 = 0 from hw.2]; norm_num⟩
      exact (hpi hwcube hz hwz) ▸ hw.2
    · intro hz0
      exact (hmeridian.symm.subset ⟨z, ⟨hz.1, hz0⟩, rfl⟩).1
  have hplane (x) (hx : x ∈ T.source) : x ∈ S ↔ (T x).2 = 0 := by
    have hq : Q x ∈ Q.target := Q.map_source (by rwa [hTs, ← hQs] at hx)
    rw [hQt] at hq
    have hz : T x ∈ Cube := hopenclosed hq
    have hpTx : p (T x) = x := (hTinv (T x)).symm.trans (T.left_inv hx)
    simpa only [hpTx] using hmer (T x) hz
  let line : ℝ → P3 := fun t => ((0, 0), 2 * t - 1)
  let gamma := p ∘ line
  have hline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : line t ∈ Cube := by
    change ((-1 ≤ (0 : ℝ) ∧ 0 ≤ 1) ∧ (-1 ≤ (0 : ℝ) ∧ 0 ≤ 1)) ∧
      (-1 ≤ 2 * t - 1 ∧ 2 * t - 1 ≤ 1)
    exact ⟨by norm_num, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hc : ContinuousOn gamma (Icc (0 : ℝ) 1) := hp.continuousOn.comp
    (show Continuous line by fun_prop).continuousOn hline
  have hzero : gamma 0 ∈ frontier (latticeHandleDomain ι κ L) := by
    simpa [gamma, line] using hend false
  have hone : gamma 1 ∈ frontier (latticeHandleDomain ι κ L) := by
    convert hend true using 1
    norm_num [gamma, line]
  have hcontact (t) (ht : t ∈ Icc (0 : ℝ) 1) (hS : gamma t ∈ S) : t = 1 / 2 := by
    have hz := (hmer (line t) (hline t ht)).mp hS
    change 2 * t - 1 = 0 at hz
    linarith
  have hball : ball (0 : P3) (1 / 2) ⊆ T.target := by
    intro z hz
    apply hTtarget
    have hn := mem_ball_zero_iff.mp hz
    simp only [Prod.norm_def, Real.norm_eq_abs, max_lt_iff] at hn
    change ((-1 < z.1.1 ∧ z.1.1 < 1) ∧ (-1 < z.1.2 ∧ z.1.2 < 1)) ∧
      (-1 < z.2 ∧ z.2 < 1)
    have h0 := abs_lt.mp hn.1.1
    have h1 := abs_lt.mp hn.1.2
    have h2 := abs_lt.mp hn.2
    exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
      ⟨by linarith, by linarith⟩⟩
  have hcross (side : Bool) : ∃ t ∈ Icc (0 : ℝ) 1,
      gamma t ∈ T.source ∧ T (gamma t) ∈ ball (0 : P3) (1 / 2) ∧
        if side then 0 < (T (gamma t)).2 else (T (gamma t)).2 < 0 := by
    let t : ℝ := if side then 5 / 8 else 3 / 8
    have ht : t ∈ Icc (0 : ℝ) 1 := by cases side <;> norm_num [t]
    have hl : line t ∈ OpenCube := by
      change ((-1 < (0 : ℝ) ∧ 0 < 1) ∧ (-1 < (0 : ℝ) ∧ 0 < 1)) ∧
        (-1 < 2 * t - 1 ∧ 2 * t - 1 < 1)
      cases side <;> norm_num [t]
    have hpz := hpT (line t) hl
    refine ⟨t, ht, hpz.1, ?_, ?_⟩
    · change T (p (line t)) ∈ _
      rw [hpz.2, mem_ball_zero_iff]
      cases side <;> norm_num [line, t, Prod.norm_def]
    · change if side then 0 < (T (p (line t))).2 else (T (p (line t))).2 < 0
      rw [hpz.2]
      cases side <;> norm_num [line, t]
  exact s.no_single_plane_chart_lattice_arc_crossing L he hdim hSR gamma hc hzero hone
    (1 / 2) hcontact T hplane (1 / 2) (by norm_num) hball hcross

theorem no_standard_meridian_compression_disk
    {ι κ α E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (p : P3 → LatticeHandleAmbient ι κ L)
    (hp : PolyhedralPLInCharts e p Cube) (hpi : InjOn p Cube)
    (himage : p '' Cube = D)
    (hboundary : ∀ z ∈ Cube, p z ∈ frontier D ↔ z ∈ frontier Cube)
    (hend : ∀ side : Bool, p ((0, 0), if side then 1 else -1) ∈
      frontier (latticeHandleDomain ι κ L))
    (hmeridian : p '' (Square ×ˢ {(0 : ℝ)}) ⊆ interior (latticeHandleDomain ι κ L))
    {d r : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d r)
    (f : E → LatticeHandleAmbient ι κ L) (hf : PolyhedralPLInCharts e f d)
    (hfi : InjOn f d) (hfR : f '' d ⊆ interior (latticeHandleDomain ι κ L))
    (hfrim : f '' r = p '' (frontier Square ×ˢ {(0 : ℝ)}))
    (hfD : (f '' d) ∩ D = p '' (frontier Square ×ˢ {(0 : ℝ)})) : False := by
  have hsquare : IsFinitePLBallPair (ℝ × ℝ) Square (frontier Square) := by
    have hI := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
    change IsFinitePLBallPair (ℝ × ℝ) (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      (frontier (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1))
    rw [frontier_prod_eq]
    simp only [isClosed_Icc.closure_eq, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    simpa only [union_comm] using hI.prod hI
  let a : (ℝ × ℝ) →ᴬ[ℝ] P3 :=
    (ContinuousAffineMap.id ℝ (ℝ × ℝ)).prod (ContinuousAffineMap.const ℝ (ℝ × ℝ) 0)
  let m := p ∘ a
  have ha (z : ℝ × ℝ) (hz : z ∈ Square) : a z ∈ Cube := ⟨hz, by norm_num [a]⟩
  have hai : Function.Injective a := fun _ _ h => congrArg Prod.fst h
  have hmi : InjOn m Square := hpi.comp hai.injOn ha
  have hm : PolyhedralPLInCharts e m Square := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hsquare
    rw [← hKs]
    exact hp.comp_finitePiecewiseAffineOn K hK
      ⟨K, hK, rfl, K.affineOnFaces_affine a⟩ (fun z hz => ha z (hKs.subset hz))
  have hmimage (U : Set (ℝ × ℝ)) : m '' U = p '' (U ×ˢ {(0 : ℝ)}) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z, 0), ⟨hz, rfl⟩, rfl⟩
    · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      rw [show t = 0 from ht]
      exact ⟨z, hz, rfl⟩
  have hmD : m '' Square ⊆ D := by
    rintro x ⟨z, hz, rfl⟩
    exact himage.subset ⟨a z, ha z hz, rfl⟩
  have hrim : m '' frontier Square = f '' r := (hmimage _).trans hfrim.symm
  have hinter : (m '' Square) ∩ (f '' d) = m '' frontier Square := by
    apply Subset.antisymm
    · rintro x ⟨hmx, hfx⟩
      rw [hmimage]
      exact hfD.subset ⟨hfx, hmD hmx⟩
    · intro x hx
      exact ⟨image_mono hsquare.1 hx, image_mono hd.1 (hrim.subset hx)⟩
  obtain ⟨s⟩ := Dehn.Annuli.nonempty_original_sphere_of_disk_union
    he.compatible hsquare hd hm hf hmi hfi hrim hinter
  have hSR : (m '' Square) ∪ (f '' d) ⊆ interior (latticeHandleDomain ι κ L) :=
    union_subset ((hmimage Square).trans_subset hmeridian) hfR
  have hmeet : ((m '' Square) ∪ (f '' d)) ∩ D = p '' (Square ×ˢ {(0 : ℝ)}) := by
    rw [← hmimage]
    apply Subset.antisymm
    · rintro x ⟨hx | hx, hxD⟩
      · exact hx
      · exact image_mono hsquare.1 ((hmimage _).symm.subset (hfD.subset ⟨hx, hxD⟩))
    · intro x hx
      exact ⟨Or.inl hx, hmD hx⟩
  exact s.no_single_meridian_in_protected_product L he hdim hSR p hp hpi himage
    hboundary hend hmeet

theorem HamiltonMarkedProtectedBall.exists_original_meridian_noncompression
    {ι κ α E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ (p : P3 → LatticeHandleAmbient ι κ L) (G : Cube ≃ₜ D),
      PolyhedralPLInCharts e p Cube ∧
      (∀ z : Cube, p z = (G z : LatticeHandleAmbient ι κ L)) ∧
      InjOn p Cube ∧ p '' Cube = D ∧
      (∀ z ∈ Cube, p z ∈ frontier D ↔ z ∈ frontier Cube) ∧
      (∀ z ∈ Cube, p z ∈ frontier (latticeHandleDomain ι κ L) ↔ |z.2| = 1) ∧
      ∀ (d r : Set E), IsFinitePLBallPair (ℝ × ℝ) d r →
        ∀ f : E → LatticeHandleAmbient ι κ L, PolyhedralPLInCharts e f d → InjOn f d →
          f '' d ⊆ interior (latticeHandleDomain ι κ L) →
          f '' r = p '' (frontier Square ×ˢ {(0 : ℝ)}) →
          (f '' d) ∩ D = p '' (frontier Square ×ˢ {(0 : ℝ)}) → False := by
  obtain ⟨p, G, hp, hval, hpi, himage, hboundary, hRboundary, _⟩ :=
    b.exists_original_disk_protected_ball_product he hdim hi
  have hend (side : Bool) : p ((0, 0), if side then 1 else -1) ∈
      frontier (latticeHandleDomain ι κ L) := by
    have hz : ((0, 0), if side then (1 : ℝ) else -1) ∈ Cube := by
      change ((-1 ≤ (0 : ℝ) ∧ 0 ≤ 1) ∧ (-1 ≤ (0 : ℝ) ∧ 0 ≤ 1)) ∧
        (-1 ≤ (if side then (1 : ℝ) else -1) ∧ (if side then (1 : ℝ) else -1) ≤ 1)
      cases side <;> norm_num
    apply (hRboundary _ hz).mpr
    cases side <;> norm_num
  have hmeridian : p '' (Square ×ˢ {(0 : ℝ)}) ⊆
      interior (latticeHandleDomain ι κ L) := by
    rintro x ⟨z, hz, rfl⟩
    have hz0 : z.2 = 0 := hz.2
    have hzc : z ∈ Cube := ⟨hz.1, by rw [hz0]; norm_num⟩
    rw [← self_sdiff_frontier]
    refine ⟨b.subset_domain (himage.subset ⟨z, hzc, rfl⟩), ?_⟩
    intro hfront
    have hh := (hRboundary z hzc).mp hfront
    norm_num [hz0] at hh
  refine ⟨p, G, hp, hval, hpi, himage, hboundary, hRboundary, ?_⟩
  intro d r hd f hf hfi hfR hfrim hfD
  exact no_standard_meridian_compression_disk L he hdim p hp hpi himage
    hboundary hend hmeridian hd f hf hfi hfR hfrim hfD

end PoincareConjecture.M76
