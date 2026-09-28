import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedBoundaryCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ChartwiseBall
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteConvexDomain
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "D0" => closedBall (0 : V3) 1
local notation "B0" => frontier (closedBall (0 : V3) 1)

private theorem exists_cube_boundary_collar_model :
    ∃ (s : Finset D0) (L : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : L.space ≃ₜ B0) (c : (s → ℝ × V3) × ℝ → V3),
      L.faces.Finite ∧ HB.IsFinitePL ∧
      FinitePiecewiseAffineOn c (L.space ×ˢ I) ∧
      Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set ((s → ℝ × V3) × ℝ)) => c z) ∧
      MapsTo c (L.space ×ˢ I) D0 ∧
      (∀ x : L.space, c ((x : s → ℝ × V3), 0) = HB x) ∧
      (∀ z : (L.space ×ˢ I : Set ((s → ℝ × V3) × ℝ)),
        c z ∈ B0 ↔ (z : (s → ℝ × V3) × ℝ).2 = 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ →
          IsOpen ((Subtype.val : D0 → V3) ⁻¹' (c '' (L.space ×ˢ Ico 0 ε))) := by
  classical
  let e := fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph
  have hball : IsFinitePLBallPair V3 D0 B0 := by
    rw [frontier_closedBall _ one_ne_zero]
    exact isFinitePLBallPair_unit_cube
  have hballcopy := hball
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hballcopy
  have hp : (1 : V3) ∈ B0 := by
    rw [frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
    simp
  have hm : (-1 : V3) ∈ B0 := by
    rw [frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm]
    simp
  have hpm : (1 : V3) ≠ -1 := by
    intro h
    have hh := congrFun h 0
    norm_num at hh
  have he : PLDomain e D0 :=
    K.plDomain_convex_of_frontier_points hK (isCompact_closedBall _ _)
      (convex_closedBall _ _) ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
      hKs hp hm hpm
  obtain ⟨b⟩ := chartwisePLBall_of_finitePLBallPair_in_chart e
    (Homeomorph.refl V3).toOpenPartialHomeomorph (fun y _ => ⟨(), mem_univ y⟩)
    (fun _ => he.compatible () ()) (ContinuousLinearEquiv.refl ℝ V3) hball (subset_univ _)
  have hb : ChartwisePLBall e D0 B0 := by simpa using b
  obtain ⟨s, L, HB, c, hL, hc, hci, hcD, hc0, hczero, δ, hδ, hδsmall, _, hopen⟩ :=
    exists_protected_small_boundary_collar (isCompact_closedBall _ _) he subset_rfl hb
      isOpen_univ (subset_univ _)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨KI, hKI, hKIs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  obtain ⟨LP, hLP, hLPs, _⟩ := L.exists_finite_triangulation_prod KI hL hKI
  rw [hKIs] at hLPs
  have hcf : FinitePiecewiseAffineOn c (L.space ×ˢ I) := by
    have h : PolyhedralPLInCharts e c LP.space := hLPs.symm ▸ hc
    have hi : ∀ i : Unit, LocallyPiecewiseAffineOn (id ∘ (e i).symm) (e i).target :=
      fun _ => locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3) isOpen_univ
    exact hLPs ▸ h.finitePiecewiseAffineOn_comp LP hLP hi
  let a : (s → ℝ × V3) →ᴬ[ℝ] (s → ℝ × V3) × ℝ :=
    (ContinuousAffineMap.id ℝ _).prod (ContinuousAffineMap.const ℝ _ 0)
  have ha : FinitePiecewiseAffineOn a L.space :=
    ⟨L, hL, rfl, L.affineOnFaces_affine a⟩
  have hHB : HB.IsFinitePL :=
    ⟨c ∘ a, hcf.comp ha (fun x hx => ⟨hx, le_rfl, zero_le_one⟩),
      fun x => (hc0 x).symm⟩
  exact ⟨s, L, HB, c, hL, hHB, hcf, hci, hcD, hc0, hczero,
    δ, hδ, hδsmall, hopen⟩





theorem _root_.Set.IsFinitePLBallPair.exists_finitePL_boundary_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D B : Set E} (hD : IsFinitePLBallPair V3 D B) :
    ∃ (f : E × ℝ → E)
      (H : (B ×ˢ I : Set (E × ℝ)) ≃ₜ f '' (B ×ˢ I)),
      H.IsFinitePL ∧ (∀ z, (H z : E) = f z) ∧ MapsTo f (B ×ˢ I) D ∧
      (∀ x ∈ B, f (x, 0) = x) ∧
      (∀ z ∈ B ×ˢ I, f z ∈ B ↔ z.2 = 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ →
          IsOpen ((Subtype.val : D → E) ⁻¹' (f '' (B ×ˢ Ico 0 ε))) := by
  classical
  obtain ⟨d, hd, hdb⟩ := hD.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  obtain ⟨_, LB, _, _, hLB, hLBs⟩ := hD.exists_finite_carrier_and_rim_complexes
  let db := d.restrictSubsets hD.1 isClosed_closedBall.frontier_subset hdb
  have hdbPL : db.IsFinitePL :=
    hd.restrictSubsets hD.1 isClosed_closedBall.frontier_subset hdb LB hLB hLBs
  obtain ⟨s, L, HB, c, hL, hHB, hc, hci, hcD, hc0, hczero, δ, hδ, hδsmall, hopen⟩ :=
    exists_cube_boundary_collar_model
  let Z : B ≃ₜ L.space := db.trans HB.symm
  have hZ : Z.IsFinitePL := hdbPL.trans hHB.symm
  obtain ⟨a, ha, haval⟩ := hZ
  obtain ⟨g, hg, hgval⟩ := hd.symm
  have haL (x : E) (hx : x ∈ B) : a x ∈ L.space :=
    (haval ⟨x, hx⟩) ▸ (Z ⟨x, hx⟩).property
  have haB (x : E) (hx : x ∈ B) : (HB ⟨a x, haL x hx⟩ : V3) = d ⟨x, hD.1 hx⟩ := by
    have hax : (⟨a x, haL x hx⟩ : L.space) = Z ⟨x, hx⟩ :=
      Subtype.ext (haval ⟨x, hx⟩).symm
    rw [hax]
    exact congrArg Subtype.val (HB.apply_symm_apply (db ⟨x, hx⟩))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨KI, hKI, hKIs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) I :=
    ⟨KI, hKI, hKIs, KI.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  have hamap : MapsTo (Prod.map a id) (B ×ˢ I) (L.space ×ˢ I) :=
    fun z hz => ⟨haL z.1 hz.1, hz.2⟩
  let f : E × ℝ → E := g ∘ c ∘ Prod.map a id
  have hf : FinitePiecewiseAffineOn f (B ×ˢ I) :=
    hg.comp (hc.comp (ha.prodMap hid) hamap) (fun z hz => hcD (hamap hz))
  have hfval (z : E × ℝ) (hz : z ∈ B ×ˢ I) :
      f z = (d.symm ⟨c (a z.1, z.2), hcD (hamap hz)⟩ : E) :=
    (hgval ⟨c (a z.1, z.2), hcD (hamap hz)⟩).symm
  have hfD : MapsTo f (B ×ˢ I) D := fun z hz => hfval z hz ▸
    (d.symm ⟨c (a z.1, z.2), hcD (hamap hz)⟩).property
  have hfi : InjOn f (B ×ˢ I) := by
    intro x hx y hy hxy
    rw [hfval x hx, hfval y hy] at hxy
    have heq := congrArg Subtype.val (d.symm.injective (Subtype.ext hxy))
    have hpair := congrArg Subtype.val (hci.injective
      (a₁ := ⟨(a x.1, x.2), hamap hx⟩) (a₂ := ⟨(a y.1, y.2), hamap hy⟩) heq)
    have hxy0 : x.1 = y.1 := by
      have hZZ : Z ⟨x.1, hx.1⟩ = Z ⟨y.1, hy.1⟩ := by
        apply Subtype.ext
        rw [haval, haval]
        exact congrArg (fun z : (s → ℝ × V3) × ℝ => z.1) hpair
      exact congrArg Subtype.val (Z.injective hZZ)
    exact Prod.ext hxy0 (congrArg (fun z : (s → ℝ × V3) × ℝ => z.2) hpair)
  let k : (B ×ˢ I : Set (E × ℝ)) → E := fun z => f z
  have hkc : Continuous k := hf.continuousOn.domRestrict
  have hki : Function.Injective k := fun x y h => Subtype.ext (hfi x.property y.property h)
  have hBc : IsCompact B := hLBs ▸ LB.isCompact_space_of_finite hLB
  let : CompactSpace (B ×ˢ I : Set (E × ℝ)) :=
    isCompact_iff_compactSpace.mp (hBc.prod isCompact_Icc)
  let H := (hkc.isClosedEmbedding hki).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (image_eq_range f (B ×ˢ I)).symm)
  have hbase (x : E) (hx : x ∈ B) : f (x, 0) = x := by
    rw [hfval (x, 0) ⟨hx, le_rfl, zero_le_one⟩]
    have hcd : (⟨c (a x, 0), hcD ⟨haL x hx, le_rfl, zero_le_one⟩⟩ : D0) =
        d ⟨x, hD.1 hx⟩ := Subtype.ext ((hc0 ⟨a x, haL x hx⟩).trans (haB x hx))
    rw [hcd, d.symm_apply_apply]
  have hzero (z : E × ℝ) (hz : z ∈ B ×ˢ I) : f z ∈ B ↔ z.2 = 0 := by
    rw [hfval z hz, hdb, d.apply_symm_apply]
    exact hczero ⟨(a z.1, z.2), hamap hz⟩
  refine ⟨f, H, ⟨f, hf, fun _ => rfl⟩, (fun _ => rfl), hfD, hbase, hzero,
    δ, hδ, hδsmall, ?_⟩
  intro ε hε hεδ
  have heq : d ⁻¹' ((Subtype.val : D0 → V3) ⁻¹' (c '' (L.space ×ˢ Ico 0 ε))) =
      (Subtype.val : D → E) ⁻¹' (f '' (B ×ˢ Ico 0 ε)) := by
    ext x
    constructor
    · rintro ⟨z, hz, hzx⟩
      let y : B := Z.symm ⟨z.1, hz.1⟩
      have hay : a y = z.1 := (haval y).symm.trans
        (congrArg Subtype.val (Z.apply_symm_apply ⟨z.1, hz.1⟩))
      have hyI : ((y : E), z.2) ∈ B ×ˢ I :=
        ⟨y.property, hz.2.1, by linarith [hz.2.2]⟩
      refine ⟨((y : E), z.2), ⟨y.property, hz.2⟩, ?_⟩
      rw [hfval _ hyI]
      have hpt : (⟨c (a y, z.2), hcD (hamap hyI)⟩ : D0) = d x := by
        apply Subtype.ext
        change c (a y, z.2) = (d x : V3)
        rw [hay]
        exact hzx
      rw [hpt, d.symm_apply_apply]
    · rintro ⟨z, hz, hzx⟩
      have hzI : z ∈ B ×ˢ I := ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩
      refine ⟨(a z.1, z.2), ⟨haL z.1 hz.1, hz.2⟩, ?_⟩
      have hsub : d.symm ⟨c (a z.1, z.2), hcD (hamap hzI)⟩ = x :=
        Subtype.ext ((hfval z hzI).symm.trans hzx)
      exact congrArg Subtype.val (d.symm.injective (hsub.trans (d.symm_apply_apply x).symm))
  rw [← heq]
  exact (hopen ε hε hεδ).preimage d.continuous

end PoincareConjecture.M76
