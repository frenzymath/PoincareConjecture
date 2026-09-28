import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskConvexChartData
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskForwardSigns









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}

private theorem actual_full_chart_formula
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    (c : E ≃ᴬ[ℝ] V) {u : Finset E} (hu : u ∈ T.ambient.faces)
    (hcard : u.card = 4) (hpu : (p : E) ∈ u) :
    ∃ A : V ≃ᵃ[ℝ] V, ∀ x ∈ convexHull ℝ (u : Set E),
      A (c x) = diskChartCoordinates ((T.pairChart p).chart x) := by
  classical
  let H := (T.pairChart p).chart
  have hustar : u ∈ (T.ambient.closedStar p).faces :=
    ⟨hu, by simpa only [Finset.insert_eq_of_mem hpu] using hu⟩
  obtain ⟨a0, ha0⟩ := T.star_affine p u hustar
  let a : V →ᴬ[ℝ] V := diskChartCoordinates.toContinuousAffineMap.comp
    (a0.comp c.symm.toContinuousAffineMap)
  let f : V → V := fun x => diskChartCoordinates (H (c.symm x))
  have hc : T.ambient.AffineOnFaces (c : E → V) :=
    T.ambient.affineOnFaces_affine c.toContinuousAffineMap
  let J := hc.embeddedImage c.injective.injOn
  let t : Finset V := u.image c
  have ht : t ∈ J.faces := by
    change t ∈ (hc.embeddedImage c.injective.injOn).faces
    rw [hc.embeddedImage_faces]
    exact ⟨u, hu, rfl⟩
  have htcard : t.card = Module.finrank ℝ V + 1 := by
    have htc : t.card = u.card := Finset.card_image_iff.mpr c.injective.injOn
    simpa [hcard, Module.finrank_prod] using htc
  have hts : convexHull ℝ (t : Set V) = c '' convexHull ℝ (u : Set E) := by
    simpa only [t, Finset.coe_image] using (hc.image_convexHull hu).symm
  have ha : EqOn a f (convexHull ℝ (t : Set V)) := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := hts.subset hx
    change diskChartCoordinates (a0 (c.symm (c y))) =
      diskChartCoordinates (H (c.symm (c y)))
    rw [c.symm_apply_apply, ← ha0 hy]
  have hinj : InjOn a.toAffineMap (convexHull ℝ (t : Set V)) := by
    intro x hx y hy hxy
    obtain ⟨x0, hx0, rfl⟩ := hts.subset hx
    obtain ⟨y0, hy0, rfl⟩ := hts.subset hy
    have hval : H x0 = H y0 := by
      apply diskChartCoordinates.injective
      simpa only [f, c.symm_apply_apply] using
        (ha (hts.symm.subset (mem_image_of_mem c hx0))).symm.trans
          (hxy.trans (ha (hts.symm.subset (mem_image_of_mem c hy0))))
    exact congrArg c (H.injOn
      (T.star_source p ((T.ambient.closedStar p).convexHull_subset_space hustar hx0))
      (T.star_source p ((T.ambient.closedStar p).convexHull_subset_space hustar hy0)) hval)
  obtain ⟨A, hAa⟩ := exists_affineEquiv_of_injective_full_simplex J ht htcard a.toAffineMap hinj
  refine ⟨A, fun x hx => ?_⟩
  have h := ha (hts.symm.subset (mem_image_of_mem c hx))
  change a.toAffineMap (c x) = f (c x) at h
  rw [← hAa] at h
  simpa only [f, H, AffineEquiv.coe_toAffineMap, c.symm_apply_apply] using h






theorem HamiltonProperDiskTriangulation.exists_incident_affine_chart_formulas
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    (c : E ≃ᴬ[ℝ] V) {s u : Finset E} (hs : s ∈ T.disk.faces)
    (hscard : s.card = 3) (hps : (p : E) ∈ s)
    (hu : u ∈ T.ambient.faces) (hucard : u.card = 4) (hsu : s ⊆ u)
    (P : V2 →ᴬ[ℝ] E) (hPi : Function.Injective P)
    (hP : ∀ x ∈ convexHull ℝ (s : Set E), P (T.inverse x) = x) :
    ∃ (A : V ≃ᵃ[ℝ] V) (B : V2 ≃ᵃ[ℝ] V2),
      (∀ x ∈ convexHull ℝ (u : Set E),
        A (c x) = diskChartCoordinates ((T.pairChart p).chart x)) ∧
      ∀ x : V2, A (c (P x)) = (B x, 0) := by
  classical
  let H := (T.pairChart p).chart
  obtain ⟨A, hA⟩ := actual_full_chart_formula T p c hu hucard (hsu hps)
  have hcomp : P.toAffineMap ∘ (T.inverse ∘ ((↑) : s → E)) = ((↑) : s → E) := by
    funext x
    exact hP x (subset_convexHull ℝ _ x.property)
  have hind : AffineIndependent ℝ (T.inverse ∘ ((↑) : s → E)) :=
    AffineIndependent.of_comp P.toAffineMap (by rw [hcomp]; exact T.disk.indep hs)
  have hspan : affineSpan ℝ (range (T.inverse ∘ ((↑) : s → E))) = ⊤ :=
    hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [hscard])
  let a : V2 →ᵃ[ℝ] V := A.toAffineMap.comp (c.toAffineEquiv.toAffineMap.comp P.toAffineMap)
  let normal : V2 →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ V2 ℝ).toAffineMap.comp a
  have hz : EqOn normal (AffineMap.const ℝ V2 (0 : ℝ))
      (range (T.inverse ∘ ((↑) : s → E))) := by
    rintro _ ⟨x, rfl⟩
    change (A (c (P (T.inverse x)))).2 = 0
    rw [hP x (subset_convexHull ℝ _ x.property),
      hA x (subset_convexHull ℝ _ (hsu x.property))]
    change (H x).2 = 0
    have hxsource : (x : E) ∈ H.source := T.star_source p
      ((T.ambient.closedStar p).subset_space
        ⟨hu, by simpa only [Finset.insert_eq_of_mem (hsu hps)] using hu⟩ (hsu x.property))
    have hxD : (x : E) ∈ D := T.disk_space.subset (T.disk.subset_space hs x.property)
    rcases (T.pairChart p).model with ⟨_, hplane⟩ | ⟨_, hplane⟩
    · exact (hplane x hxsource).mp hxD
    · exact ((hplane x hxsource).mp hxD).2
  have hnormal : normal = AffineMap.const ℝ V2 (0 : ℝ) := AffineMap.ext_on hspan hz
  have hzero (x : V2) : (A (c (P x))).2 = 0 :=
    congrArg (fun f : V2 →ᵃ[ℝ] ℝ => f x) hnormal
  let tangent : V2 →ᵃ[ℝ] V2 := (LinearMap.fst ℝ V2 ℝ).toAffineMap.comp a
  have hti : Function.Injective tangent := by
    intro x y hxy
    apply hPi
    apply c.injective
    apply A.injective
    apply Prod.ext
    · exact hxy
    · rw [hzero x, hzero y]
  have hlin : Function.Injective tangent.linear := tangent.linear_injective_iff.mpr hti
  have hbi : Function.Bijective tangent := tangent.linear_bijective_iff.mp
    ⟨hlin, LinearMap.injective_iff_surjective.mp hlin⟩
  let B : V2 ≃ᵃ[ℝ] V2 := AffineEquiv.ofBijective hbi
  refine ⟨A, B, hA, fun x => ?_⟩
  apply Prod.ext
  · rfl
  · exact hzero x

end PoincareConjecture.M76.HamiltonIndexOne
