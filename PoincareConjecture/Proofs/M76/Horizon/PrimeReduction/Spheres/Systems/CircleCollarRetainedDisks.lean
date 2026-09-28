import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusRegion
import PoincareConjecture.Proofs.M76.Triangulation.ConvexSphereDiskComplement
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.ClippedSphereParameter
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.TaperingCapAnnuli
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalSphereChartCarrier
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedTubeSigns

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Annulus" => squareAnnulus 8 1

theorem exists_unitCube_sphere_annulus_retained_disks
    {B : Set V3} (c : Annulus ≃ₜ B) (hc : c.IsFinitePL)
    (hBS : B ⊆ Sphere) (p : Sphere) (hpB : (p : V3) ∉ B) :
    ∃ k : Bool → Set V3,
      (∀ b, IsFinitePLBallPair P2 (k b)
          ((fun z : Annulus => (c z : V3)) '' {z | depth 8 z = if b then 1 else -1}) ∧
        k b ⊆ Sphere ∧ k b ∩ B =
          (fun z : Annulus => (c z : V3)) '' {z | depth 8 z = if b then 1 else -1}) ∧
      Disjoint (k true) (k false) ∧ (k true ∪ k false) ∪ B = Sphere := by
  classical
  obtain ⟨h, hh, hch⟩ := hc
  have hBc : IsCompact B := by
    have him : h '' Annulus = B := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [← hch ⟨x, hx⟩]
        exact (c ⟨x, hx⟩).property
      · intro hy
        exact ⟨c.symm ⟨y, hy⟩, (c.symm ⟨y, hy⟩).property,
          (hch _).symm.trans (congrArg Subtype.val (c.apply_symm_apply _))⟩
    rw [← him]
    exact hh.isCompact.image_of_continuousOn hh.continuousOn
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hsphere : Sphere = frontier (closedBall (0 : V3) 1) := by
    rw [frontier_closedBall _ one_ne_zero]
  obtain ⟨A, qA, hA, hAS, hBA, hpA, hopen⟩ :=
    K.exists_convex_frontier_disk_of_compact_with_open_interior hK
      (isCompact_closedBall (0 : V3) 1) (convex_closedBall (0 : V3) 1)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
      (hKs.trans hsphere) (F := P2) (by simp [Module.finrank_prod])
      ⟨p, hsphere.subset p.property⟩ hBc (hBS.trans hsphere.subset) hpB
  rw [← hsphere] at hAS
  obtain ⟨_, C, _, hCcv, _, F, hF, hFboundary⟩ := hA
  obtain ⟨f, hf, hFf⟩ := hF
  obtain ⟨g, hg, hGg⟩ := (show F.IsFinitePL from ⟨f, hf, hFf⟩).symm
  have hgf : LeftInvOn g f A := by
    intro x hx
    rw [← hFf ⟨x, hx⟩, ← hGg, F.symm_apply_apply]
  have hfg : LeftInvOn f g C := by
    intro x hx
    rw [← hGg ⟨x, hx⟩, ← hFf, F.apply_symm_apply]
  have hfC (x : V3) (hx : x ∈ A) : f x ∈ C := by
    rw [← hFf ⟨x, hx⟩]
    exact (F ⟨x, hx⟩).property
  have hgA (x : P2) (hx : x ∈ C) : g x ∈ A := by
    rw [← hGg ⟨x, hx⟩]
    exact (F.symm ⟨x, hx⟩).property
  have hhB (z : P2) (hz : z ∈ Annulus) : h z ∈ B := by
    rw [← hch ⟨z, hz⟩]
    exact (c ⟨z, hz⟩).property
  have hfh : FinitePiecewiseAffineOn (f ∘ h) Annulus :=
    hf.comp hh (fun x hx => (hBA (hhB x hx)).1)
  have hfhi : InjOn (f ∘ h) Annulus := by
    intro x hx y hy hxy
    have hxy' := hgf.injOn (hBA (hhB x hx)).1 (hBA (hhB y hy)).1 hxy
    exact congrArg Subtype.val (c.injective (Subtype.ext
      ((hch ⟨x, hx⟩).trans (hxy'.trans (hch ⟨y, hy⟩).symm))))
  obtain ⟨e, he, heval⟩ := hfh.exists_homeomorph_image hfhi
  have hfhim : (f ∘ h) '' Annulus = f '' B := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨h z, hhB z hz, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨c.symm ⟨x, hx⟩, (c.symm ⟨x, hx⟩).property, ?_⟩
      rw [Function.comp_apply, ← hch, c.apply_symm_apply]
  let e' := e.trans (Homeomorph.setCongr hfhim)
  have he' : e'.IsFinitePL := by
    obtain ⟨z, hz, hev⟩ := he
    exact ⟨z, hz, hev⟩
  have he'val (z : Annulus) : (e' z : P2) = f (c z) :=
    (heval z).trans (congrArg f (hch z).symm)
  obtain ⟨m, n, P, I, reverse, hP, hPi, hI, hIi, hnest, hregion, houter, hinner, _⟩ :=
    _root_.Dehn.exists_polygon_collar_of_square_annulus
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8) e' he'
  have hPB : P.boundary ℝ ⊆ f '' B := by
    rw [hregion]
    intro x hx
    refine ⟨(P.isFinitePLBallPair_closed_inside hP hPi).1 hx, ?_⟩
    intro hxI
    exact (hnest (subset_closure hxI)).1 hx
  have hBint : f '' B ⊆ interior C := by
    rintro _ ⟨x, hx, rfl⟩
    have hxA := hBA hx
    by_contra hn
    have hfr : f x ∈ frontier C := ⟨subset_closure (hfC x hxA.1), hn⟩
    apply hxA.2
    exact (hFboundary ⟨x, hxA.1⟩).mpr (by rwa [hFf])
  have hPC : closure P.inside ⊆ interior C := P.closure_inside_subset_convex hP hPi
    hCcv.interior (by
      rintro _ ⟨i, rfl⟩
      exact hBint (hPB (mem_iUnion.mpr ⟨i, left_mem_affineSegment ℝ _ _⟩)))
  have hIC : closure I.inside ⊆ C :=
    (hnest.trans subset_closure).trans (hPC.trans interior_subset)
  have hPC' : closure P.inside ⊆ C := hPC.trans interior_subset
  let di : Set V3 := g '' closure I.inside
  let ri : Set V3 := g '' I.boundary ℝ
  let do' : Set V3 := g '' closure P.inside
  let ro : Set V3 := g '' P.boundary ℝ
  have hdi : IsFinitePLBallPair P2 di ri := by
    obtain ⟨J, hJ⟩ := I.exists_triangulation hI hIi
    have hgd : FinitePiecewiseAffineOn g (closure I.inside) := by
      rw [← hJ.space_eq]
      exact hg.restrict J hJ.finite_faces (hJ.space_eq.subset.trans hIC)
    exact (I.isFinitePLBallPair_closed_inside hI hIi).image hgd (hfg.injOn.mono hIC)
  have hdo : IsFinitePLBallPair P2 do' ro := by
    obtain ⟨J, hJ⟩ := P.exists_triangulation hP hPi
    have hgd : FinitePiecewiseAffineOn g (closure P.inside) := by
      rw [← hJ.space_eq]
      exact hg.restrict J hJ.finite_faces (hJ.space_eq.subset.trans hPC')
    exact (P.isFinitePLBallPair_closed_inside hP hPi).image hgd (hfg.injOn.mono hPC')
  have hdiS : di ⊆ Sphere := by
    rintro _ ⟨x, hx, rfl⟩
    exact hAS (hgA x (hIC hx))
  have hdoA : do' ⊆ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact hgA x (hPC' hx)
  have hdoS : do' ⊆ Sphere := hdoA.trans hAS
  have hclosed_inside (Q : Polygon P2 (n + 3)) (hQ : Q.HasSimplicialEdges)
      (hQi : Function.Injective Q) : closure Q.inside \ Q.boundary ℝ = Q.inside := by
    rw [closure_eq_self_union_frontier, Q.frontier_inside hQ hQi]
    ext x
    simp only [mem_sdiff, mem_union]
    have hnot := fun hx : x ∈ Q.inside => hx.1
    tauto
  have hini : di \ ri = g '' I.inside := by
    change g '' closure I.inside \ g '' I.boundary ℝ = _
    rw [← Set.InjOn.image_sdiff_subset (hfg.injOn.mono hIC)
      (I.isFinitePLBallPair_closed_inside hI hIi).1, hclosed_inside I hI hIi]
  have hino : do' \ ro = g '' P.inside := by
    change g '' closure P.inside \ g '' P.boundary ℝ = _
    rw [← Set.InjOn.image_sdiff_subset (hfg.injOn.mono hPC')
      (P.isFinitePLBallPair_closed_inside hP hPi).1]
    rw [closure_eq_self_union_frontier, P.frontier_inside hP hPi]
    congr 1
    ext x
    have hnot := fun hx : x ∈ P.inside => hx.1
    simp only [mem_sdiff, mem_union]
    tauto
  have hnest' : di ⊆ do' \ ro := by
    rw [hino]
    exact image_mono hnest
  have hB : B = do' \ (di \ ri) := by
    have hgfB : g '' (f '' B) = B := by
      rw [image_image]
      exact (image_congr (fun x hx => hgf (hBA hx).1)).trans (image_id B)
    rw [← hgfB, hregion, hini]
    exact Set.InjOn.image_sdiff_subset (hfg.injOn.mono hPC')
      (fun x hx => subset_closure (hnest (subset_closure hx)))
  let extDisk : Set V3 := Sphere \ (do' \ ro)
  have hext : IsFinitePLBallPair P2 extDisk ro := by
    have h := K.isFinitePLBallPair_convex_sphere_disk_complement hK
      (isCompact_closedBall (0 : V3) 1) (convex_closedBall (0 : V3) 1)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
      (hKs.trans hsphere) (by simp) hdo (hdoS.trans hsphere.subset)
      ⟨p, hsphere.subset p.property, fun hx => hpA (hdoA hx)⟩
    simpa only [← hsphere, extDisk] using h
  have hriB : ri ⊆ B := by
    rw [hB]
    intro x hx
    exact ⟨(hnest' (hdi.1 hx)).1, fun h => h.2 hx⟩
  have hroB : ro ⊆ B := by
    rw [hB]
    intro x hx
    refine ⟨hdo.1 hx, ?_⟩
    intro h
    exact (hnest' h.1).2 hx
  have hdiB : di ∩ B = ri := by
    rw [hB]
    ext x
    have hir := @hdi.1 x
    have hid := fun hx : x ∈ di => (hnest' hx).1
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  have hextB : extDisk ∩ B = ro := by
    rw [hB]
    ext x
    have hro := @hdo.1 x
    have hroS := fun hx : x ∈ ro => hdoS (hdo.1 hx)
    have hri := fun hx : x ∈ di => (hnest' hx).2
    simp only [extDisk, mem_inter_iff, mem_sdiff]
    tauto
  have hdisjoint : Disjoint di extDisk :=
    Set.disjoint_left.mpr (fun _ hx hy => hy.2 (hnest' hx))
  have hwhole : (di ∪ extDisk) ∪ B = Sphere := by
    rw [hB]
    ext x
    have hi := @hdiS x
    have ho := @hdoS x
    simp only [extDisk, mem_union, mem_sdiff]
    tauto
  have hriLabel : ri = (fun z : Annulus => (c z : V3)) ''
      {z | depth 8 z = if reverse then -1 else 1} := by
    ext x
    constructor
    · intro hx
      let z := c.symm ⟨x, hriB hx⟩
      have hcz : (c z : V3) = x := congrArg Subtype.val (c.apply_symm_apply _)
      refine ⟨z, ?_, hcz⟩
      apply (hinner z).mp
      obtain ⟨y, hy, hyx⟩ := hx
      rw [he'val, hcz, ← hyx, hfg (hIC ((I.isFinitePLBallPair_closed_inside hI hIi).1 hy))]
      exact hy
    · rintro ⟨z, hz, rfl⟩
      have hi := (hinner z).mpr hz
      rw [he'val] at hi
      exact ⟨f (c z), hi, hgf (hBA (c z).property).1⟩
  have hroLabel : ro = (fun z : Annulus => (c z : V3)) ''
      {z | depth 8 z = if reverse then 1 else -1} := by
    ext x
    constructor
    · intro hx
      let z := c.symm ⟨x, hroB hx⟩
      have hcz : (c z : V3) = x := congrArg Subtype.val (c.apply_symm_apply _)
      refine ⟨z, ?_, hcz⟩
      apply (houter z).mp
      obtain ⟨y, hy, hyx⟩ := hx
      rw [he'val, hcz, ← hyx, hfg (hPC' ((P.isFinitePLBallPair_closed_inside hP hPi).1 hy))]
      exact hy
    · rintro ⟨z, hz, rfl⟩
      have ho := (houter z).mpr hz
      rw [he'val] at ho
      exact ⟨f (c z), ho, hgf (hBA (c z).property).1⟩
  let k : Bool → Set V3 := fun b => if b = reverse then extDisk else di
  refine ⟨k, ?_, ?_, ?_⟩
  · intro b
    cases reverse <;> cases b <;> simp only [k, Bool.false_eq_true, Bool.true_eq_false,
      if_false, if_true] at * <;>
      first | exact ⟨hroLabel ▸ hext, sdiff_subset, hextB.trans hroLabel⟩ |
        exact ⟨hriLabel ▸ hdi, hdiS, hdiB.trans hriLabel⟩
  · cases reverse <;> simp only [k, Bool.false_eq_true, Bool.true_eq_false, if_false, if_true]
    · exact hdisjoint
    · exact hdisjoint.symm
  · cases reverse <;> simp only [k, Bool.false_eq_true, Bool.true_eq_false, if_false, if_true]
    · exact hwhole
    · simpa only [union_comm extDisk di] using hwhole

private noncomputable def sphereStripQuarterCoordinates (β : ℝ) : P2 →ᴬ[ℝ] P2 :=
  (((1 / 4 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).prod
    ((β / 32) • ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap

private theorem sphereStripQuarterCoordinates_apply (β : ℝ) (z : P2) :
    sphereStripQuarterCoordinates β z = (z.2 / 4, β / 32 * z.1) := by
  ext <;> simp [sphereStripQuarterCoordinates] <;> ring

theorem exists_retained_disks_of_sphere_strip {β : ℝ} (hβ : 0 < β)
    (φ : P2 → V3)
    (hφ : FinitePiecewiseAffineOn φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β))
    (hφS : MapsTo φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) Sphere)
    (hfib : ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      ∀ y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      φ x = φ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0))) :
    ∃ k : Bool → Set V3,
      (∀ b, IsFinitePLBallPair P2 (k b)
          ((fun t : ℝ => φ (if b then 1 / 4 else -1 / 4, t)) '' Icc 0 β) ∧
        k b ⊆ Sphere ∧
        k b ∩ (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)) =
          (fun t : ℝ => φ (if b then 1 / 4 else -1 / 4, t)) '' Icc 0 β ∧
        Disjoint (k b) ((fun t : ℝ => φ (0, t)) '' Icc 0 β)) ∧
      Disjoint (k true) (k false) ∧
      (k true ∪ k false) ∪ (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)) = Sphere := by
  classical
  let : Fact (0 < (4 * 8 : ℝ)) := ⟨by norm_num⟩
  let Cβ := sphereStripQuarterCoordinates β
  have hCval (z : P2) : Cβ z = (z.2 / 4, β / 32 * z.1) :=
    sphereStripQuarterCoordinates_apply β z
  have hCmap : MapsTo Cβ (Icc 0 (4 * 8) ×ˢ Icc (-1) 1)
      (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    rw [hCval]
    refine ⟨⟨by dsimp; linarith [hu.1], by dsimp; linarith [hu.2]⟩,
      mul_nonneg (by positivity) hs.1, ?_⟩
    dsimp
    nlinarith [hs.2]
  have hC : FinitePiecewiseAffineOn Cβ (Icc 0 (4 * 8) ×ˢ Icc (-1) 1) := by
    have hbox := (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 4 * 8)).prod
      (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := hbox
    exact ⟨J, hJ, hJs, J.affineOnFaces_affine Cβ⟩
  have hψ : FinitePiecewiseAffineOn (φ ∘ Cβ) (Icc 0 (4 * 8) ×ˢ Icc (-1) 1) :=
    hφ.comp hC hCmap
  have hfib' : ∀ x ∈ Icc 0 (4 * 8) ×ˢ Icc (-1) 1,
      ∀ y ∈ Icc 0 (4 * 8) ×ˢ Icc (-1) 1,
      (φ ∘ Cβ) x = (φ ∘ Cβ) y ↔ x.2 = y.2 ∧
        (x.1 : AddCircle (4 * 8 : ℝ)) = (y.1 : AddCircle (4 * 8 : ℝ)) := by
    intro x hx y hy
    have ht (s t : ℝ) : β / 32 * s = β / 32 * t ↔ s = t :=
      mul_right_inj' (by positivity)
    have hzero (s : ℝ) : β / 32 * s = 0 ↔ s = 0 := by
      simpa only [mul_zero] using ht s 0
    have hend (s : ℝ) : β / 32 * s = β ↔ s = 4 * 8 := by
      have heq : β / 32 * (4 * 8) = β := by ring
      simpa only [heq] using ht s (4 * 8)
    rw [Function.comp_apply, Function.comp_apply, hfib _ (hCmap hx) _ (hCmap hy),
      hCval, hCval, AddCircle.coe_eq_coe_iff_eq_or_endpoints hx.1 hy.1]
    change x.2 / 4 = y.2 / 4 ∧
      (β / 32 * x.1 = β / 32 * y.1 ∨
        (β / 32 * x.1 = 0 ∧ β / 32 * y.1 = β) ∨
        (β / 32 * x.1 = β ∧ β / 32 * y.1 = 0)) ↔ _
    rw [div_left_inj' (by norm_num : (4 : ℝ) ≠ 0), ht, hzero, hend, hend, hzero]
  obtain ⟨c, hc, hci, hperiod, hdepth⟩ :=
    _root_.Dehn.exists_finitePL_annulus_of_periodic_strip
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8)
      (φ ∘ Cβ) hψ hfib'
  have hBS : (φ ∘ Cβ) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1) ⊆ Sphere := by
    rintro _ ⟨z, hz, rfl⟩
    exact hφS (hCmap hz)
  let p : Sphere := ⟨φ (1 / 2, 0), hφS ⟨by norm_num, ⟨le_rfl, hβ.le⟩⟩⟩
  have hpB : (p : V3) ∉ (φ ∘ Cβ) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1) := by
    rintro ⟨z, hz, heq⟩
    have hfirst := ((hfib _ (hCmap hz) (1 / 2, 0)
      ⟨by norm_num, ⟨le_rfl, hβ.le⟩⟩).mp heq).1
    rw [hCval] at hfirst
    change z.2 / 4 = 1 / 2 at hfirst
    linarith [hz.2.2]
  obtain ⟨k, hk, hdisjoint, hwhole⟩ :=
    exists_unitCube_sphere_annulus_retained_disks c hc hBS p hpB
  have hBimage : (φ ∘ Cβ) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1) =
      φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β) := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨Cβ z, ?_, rfl⟩
      rw [hCval]
      exact ⟨⟨by dsimp; linarith [hz.2.1], by dsimp; linarith [hz.2.2]⟩, (hCmap hz).2⟩
    · rintro _ ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
      refine ⟨(32 * (t / β), 4 * u), ⟨⟨mul_nonneg (by norm_num) (div_nonneg ht.1 hβ.le), ?_⟩,
        ⟨by dsimp; linarith [hu.1], by dsimp; linarith [hu.2]⟩⟩, ?_⟩
      · have hb : t / β ≤ 1 := (div_le_one hβ).mpr ht.2
        dsimp
        nlinarith
      · change φ (Cβ _) = _
        rw [hCval]
        congr 1
        ext <;> dsimp <;> field_simp
  have hlabel (b : Bool) :
      (fun z : Annulus => (c z : V3)) '' {z | depth 8 z = if b then 1 else -1} =
        (fun t : ℝ => φ (if b then 1 / 4 else -1 / 4, t)) '' Icc 0 β := by
    have hrescale := cap_circle_period_rescaling hβ
      (fun z : P2 × ℝ => φ (z.1.1, z.2)) ((if b then 1 / 4 else -1 / 4), 0)
    change (fun s : ℝ => φ ((if b then 1 / 4 else -1 / 4), β / 32 * s)) '' Icc 0 (4 * 8) = _ at hrescale
    rw [← hrescale]
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs, hsz⟩ := exists_period_parameter_of_depth
        (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8) z
      refine ⟨s, hs, ?_⟩
      have hv := hdepth z s hs hsz
      rw [Function.comp_apply, hCval] at hv
      change (c z : V3) = φ (depth 8 z / 4, β / 32 * s) at hv
      rw [hz] at hv
      cases b <;> norm_num at hv ⊢ <;> exact hv.symm
    · rintro _ ⟨s, hs, rfl⟩
      let u : Icc (-1 : ℝ) 1 := ⟨if b then 1 else -1, by cases b <;> norm_num⟩
      let z : Annulus := ⟨annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)), u),
        _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩
      refine ⟨z, ?_, ?_⟩
      · change depth 8 (annulusMap 8 (by norm_num) ((s : AddCircle (4 * 8 : ℝ)), (u : ℝ))) = _
        rw [depth_annulusMap (by norm_num) (by cases b <;> norm_num [u])]
      · have hv := hperiod s hs u
        rw [Function.comp_apply, hCval] at hv
        change (c z : V3) = φ ((u : ℝ) / 4, β / 32 * s) at hv
        cases b <;> norm_num [u] at hv ⊢ <;> exact hv
  refine ⟨k, ?_, hdisjoint, ?_⟩
  · intro b
    obtain ⟨hkb, hkS, hkB⟩ := hk b
    change k b ∩ ((φ ∘ Cβ) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1)) = _ at hkB
    rw [hlabel] at hkb hkB
    rw [hBimage] at hkB
    refine ⟨hkb, hkS, hkB, ?_⟩
    apply Set.disjoint_left.mpr
    rintro x hx ⟨t, ht, htx⟩
    have hxB : x ∈ φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β) :=
      ⟨(0, t), ⟨by norm_num, ht⟩, htx⟩
    obtain ⟨s, hs, hsx⟩ := hkB.subset ⟨hx, hxB⟩
    have he := ((hfib (if b then 1 / 4 else -1 / 4, s)
      ⟨by cases b <;> norm_num, hs⟩ (0, t) ⟨by norm_num, ht⟩).mp (hsx.trans htx.symm)).1
    cases b <;> norm_num at he
  · change (k true ∪ k false) ∪ ((φ ∘ Cβ) '' (Icc 0 (4 * 8) ×ˢ Icc (-1) 1)) = _ at hwhole
    rwa [hBimage] at hwhole

theorem ChartwisePLSphere.exists_circle_collar_retained_disks
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    {β : ℝ} (hβ : 0 < β) (σ : P2 × ℝ → V3)
    (hσ : FinitePiecewiseAffineOn σ (PoincareConjecture.M76.Dehn.signedTubeDiamond ×ˢ Icc 0 β))
    (hσJ : MapsTo σ (PoincareConjecture.M76.Dehn.signedTubeDiamond ×ˢ Icc 0 β) J.space)
    (hσS : ∀ z ∈ PoincareConjecture.M76.Dehn.signedTubeDiamond ×ˢ Icc 0 β,
      z.1.2 = 0 → Q.symm (σ z) ∈ S)
    (hfib : ∀ x ∈ PoincareConjecture.M76.Dehn.signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ PoincareConjecture.M76.Dehn.signedTubeDiamond ×ˢ Icc 0 β,
      σ x = σ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0))) :
    ∃ (φ : P2 → V3) (k : Bool → Set V3),
      FinitePiecewiseAffineOn φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) ∧
      MapsTo φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) Sphere ∧
      (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β, s.map (φ z) = Q.symm (σ ((z.1, 0), z.2))) ∧
      (∀ b,
        let r := (fun t : ℝ => φ (if b then 1 / 4 else -1 / 4, t)) '' Icc 0 β
        IsFinitePLBallPair P2 (k b) r ∧ k b ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (k b \ r)) r ∧
        PolyhedralPLInCharts e s.map (k b) ∧
        PolyhedralPLInCharts e s.map (Sphere \ (k b \ r)) ∧
        s.map '' r = (fun t : ℝ => Q.symm (σ ((if b then 1 / 4 else -1 / 4, 0), t))) '' Icc 0 β ∧
        k b ∩ (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)) = r ∧
        Disjoint (k b) ((fun t : ℝ => φ (0, t)) '' Icc 0 β)) ∧
      Disjoint (k true) (k false) ∧
      (k true ∪ k false) ∪ (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)) = Sphere := by
  classical
  obtain ⟨P, hP, hPs, _, hPmem⟩ := s.exists_finite_chart_carrier Q hQ J hJ hJQ
  obtain ⟨g, hg, hgS, hgi, hright, _, _⟩ :=
    s.exists_finite_clipped_parameter Q hQ J P hJ hJQ hP hPs
  let F := PoincareConjecture.M76.Dehn.signedSheetStripMap (1 : Fin 2)
  have hFval (z : P2) : F z = ((z.1, 0), z.2) := by
    simp [F, PoincareConjecture.M76.Dehn.signedSheetStripMap_apply]
  have hFmap : MapsTo F (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β)
      (PoincareConjecture.M76.Dehn.signedTubeDiamond ×ˢ Icc 0 β) :=
    fun _ hz => PoincareConjecture.M76.Dehn.signedSheetStripMap_mem (1 : Fin 2) hz
  have hσFP (z : P2) (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) : σ (F z) ∈ P.space := by
    apply (hPmem _ (hσJ (hFmap hz))).mp
    exact hσS _ (hFmap hz) (by rw [hFval])
  let φ : P2 → V3 := g ∘ σ ∘ F
  have hφ : FinitePiecewiseAffineOn φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) :=
    hg.comp (hσ.comp (PoincareConjecture.M76.Dehn.signedSheetStripMap_finitePL hβ 1) hFmap) hσFP
  have hφS : MapsTo φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) Sphere :=
    fun _ hz => hgS (hσFP _ hz)
  have hφval (z : P2) (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) :
      s.map (φ z) = Q.symm (σ ((z.1, 0), z.2)) := by
    change s.map (g (σ (F z))) = _
    rw [hright _ (hσFP z hz), hFval]
  have hφfib : ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      ∀ y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      φ x = φ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)) := by
    intro x hx y hy
    change g (σ (F x)) = g (σ (F y)) ↔ _
    rw [hgi.eq_iff (hσFP x hx) (hσFP y hy), hfib _ (hFmap hx) _ (hFmap hy), hFval, hFval]
    simp only [Prod.mk.injEq, and_true]
  obtain ⟨k, hk, hdisjoint, hwhole⟩ := exists_retained_disks_of_sphere_strip hβ φ hφ hφS hφfib
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hsphere : Sphere = frontier (closedBall (0 : V3) 1) := by
    rw [frontier_closedBall _ one_ne_zero]
  have hPL {d q : Set V3} (hd : IsFinitePLBallPair P2 d q) (hdS : d ⊆ Sphere) :
      PolyhedralPLInCharts e s.map d := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ := hd
    rw [← hLs]
    exact s.piecewiseAffine.restrict_finite L hL (hLs.subset.trans hdS)
  refine ⟨φ, k, hφ, hφS, hφval, ?_, hdisjoint, hwhole⟩
  intro b
  obtain ⟨hkb, hkS, hkB, hkaxis⟩ := hk b
  let r := (fun t : ℝ => φ (if b then 1 / 4 else -1 / 4, t)) '' Icc 0 β
  have hcomp : IsFinitePLBallPair P2 (Sphere \ (k b \ r)) r := by
    have h := K.isFinitePLBallPair_convex_sphere_disk_complement hK
      (isCompact_closedBall (0 : V3) 1) (convex_closedBall (0 : V3) 1)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩
      (hKs.trans hsphere) (by simp) hkb (hkS.trans hsphere.subset)
      ⟨φ (0, 0), hsphere.subset (hφS ⟨by norm_num, ⟨le_rfl, hβ.le⟩⟩), ?_⟩
    · simpa only [← hsphere, r] using h
    · intro hx
      exact Set.disjoint_left.mp hkaxis hx ⟨0, ⟨le_rfl, hβ.le⟩, rfl⟩
  refine ⟨hkb, hkS, hcomp, hPL hkb hkS, hPL hcomp sdiff_subset, ?_, hkB, hkaxis⟩
  rw [image_image]
  apply image_congr
  intro t ht
  exact hφval (if b then 1 / 4 else -1 / 4, t) ⟨by cases b <;> norm_num, ht⟩

end PoincareConjecture.M76
