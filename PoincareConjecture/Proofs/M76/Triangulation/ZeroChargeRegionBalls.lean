import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeSphereCollars
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargePlanarDiskFamily
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeCollarCapStep
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargePairedCapEndpoints
import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereGenericSweep
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexThreeRegionSupplier










set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem hasZeroChargeAlexanderRegionBalls (hdim : Module.finrank ℝ E = 3) :
    HasZeroChargeAlexanderRegionBalls E := by
  classical
  intro C hC hCcv _hne J hJ hJC W hsigns _hfinite hzero hWC hmodel
  obtain ⟨e, he⟩ := hmodel
  have hhalf : IsCompact (halfBall 1) := isCompact_halfBall (Or.inl rfl)
  have hhalfCv : Convex ℝ (halfBall 1) := by
    rw [halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage (halfBallForms 1 i)
  have hhalfNe : (interior (halfBall 1)).Nonempty := interior_halfBall_nonempty (Or.inl rfl)
  have hdimHalf : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by simp
  obtain ⟨K, hK, hKS, _, hpure, hcofaces, hlinks⟩ :=
    he.exists_height_aligned_surface_complex hhalf hhalfCv hhalfNe hdimHalf W.height
  let eK : K.space ≃ₜ frontier (halfBall 1) := (Homeomorph.setCongr hKS).trans e
  have heK : eK.IsFinitePL := (Homeomorph.isFinitePL_setCongr hKS K hK rfl).trans he
  have hKC : K.space ⊆ interior C := hKS.symm ▸ hWC
  have hpres : ∀ c, HasAlexanderCurvePresentation (K.space ∩ {x | W.height x = c}) 0 := by
    intro c
    simpa only [hKS, hzero c] using W.presentation c
  have hsignsK : ∀ x ∈ K.space,
      x ∈ closure ((K.space ∩ {y | W.height y = W.height x}) \ {x}) →
        x ∈ closure (K.space ∩ {y | W.height y < W.height x}) ∧
          x ∈ closure (K.space ∩ {y | W.height x < W.height y}) := by
    simpa only [hKS, AlexanderSectionProfile.HasNonisolatedHeightSigns] using hsigns
  obtain ⟨B, p, q, hBlinear, hBgeneric, hp, hq, hpq, hBbound, hBmin, hBmax,
      _, hBpolygons, hBsigns, _⟩ :=
    K.exists_generic_single_polygon_height_of_zero_charge hK hpure hcofaces hlinks
      heK hhalf hhalfCv hhalfNe hdimHalf W.height hpres hsignsK
  let A : E →ᵃ[ℝ] ℝ := B - AffineMap.const ℝ E (B p)
  have hAx (x : E) : A x = B x - B p := rfl
  have hAlinear : A.linear ≠ 0 := by simpa [A] using hBlinear
  have hAgeneric : InjOn A K.vertices := by
    intro x hx y hy hxy
    apply hBgeneric hx hy
    exact sub_left_inj.mp (show B x - B p = B y - B p from hxy)
  have hpA : A p = 0 := by rw [hAx, sub_self]
  have hqA : 0 < A q := by rw [hAx]; exact sub_pos.mpr hpq
  have hmin (x : E) (hx : x ∈ K.space) : 0 ≤ A x := by
    rw [hAx]
    exact sub_nonneg.mpr (hBbound x hx).1
  have hmax (x : E) (hx : x ∈ K.space) : A x ≤ A q := by
    rw [hAx, hAx]
    exact sub_le_sub_right (hBbound x hx).2 _
  have hminfiber : K.space ∩ {x | A x = 0} = {p} := by
    simpa only [hAx, sub_eq_zero] using hBmin
  have hmaxfiber : K.space ∩ {x | A x = A q} = {q} := by
    simpa only [hAx, sub_left_inj] using hBmax
  have hpolygons : ∀ c ∈ Ioo (0 : ℝ) (A q), ∃ (n : ℕ) (P : Polygon E (n + 3)),
      P.HasSimplicialEdges ∧ Function.Injective P ∧
        P.boundary ℝ = K.space ∩ {x | A x = c} := by
    intro c hc
    have hcB : c + B p ∈ Ioo (B p) (B q) := by
      constructor <;> linarith [hc.1, hc.2, hAx q]
    obtain ⟨n, P, hPi, hPe, hPs⟩ := hBpolygons (c + B p) hcB
    refine ⟨n, P, hPe, hPi, hPs.trans ?_⟩
    apply congrArg (fun T : Set E => K.space ∩ T)
    ext x
    change B x = c + B p ↔ A x = c
    rw [hAx]
    constructor <;> intro hx <;> linarith
  obtain ⟨disks, hdisks⟩ :=
    ZeroChargeJoint.exists_planar_disk_family_of_whole_level_polygons hdim A hAlinear hpolygons
  have hlocal : ∀ c ∈ Ioo (0 : ℝ) (A q), ∃ ε : ℝ, 0 < ε ∧
      ∀ u v : ℝ, u ∈ Ioo (0 : ℝ) (A q) → v ∈ Ioo (0 : ℝ) (A q) →
        |u - c| ≤ ε → |v - c| ≤ ε → u ≤ v →
          ZeroChargeJoint.HasPairedHeightCap K.space C (disks u) A u →
            ZeroChargeJoint.HasPairedHeightCap K.space C (disks v) A v := by
    intro c hc
    obtain ⟨n, P, hP, hPi, hPs⟩ := hpolygons c hc
    have hsignsc : ∀ x ∈ K.space, A x = c →
        x ∈ closure (K.space ∩ {y | A y < c}) ∧
          x ∈ closure (K.space ∩ {y | c < A y}) := by
      intro x hx hxc
      have hxlo : B p < B x := by linarith [hc.1, hAx x]
      have hxhi : B x < B q := by linarith [hc.2, hAx x, hAx q]
      have hsignsB := hBsigns x hx hxlo hxhi
      have hlow : K.space ∩ {y | A y < c} = K.space ∩ {y | B y < B x} := by
        ext y
        change y ∈ K.space ∧ A y < c ↔ y ∈ K.space ∧ B y < B x
        rw [← hxc, hAx, hAx, sub_lt_sub_iff_right]
      have hhigh : K.space ∩ {y | c < A y} = K.space ∩ {y | B x < B y} := by
        ext y
        change y ∈ K.space ∧ c < A y ↔ y ∈ K.space ∧ B x < B y
        rw [← hxc, hAx, hAx, sub_lt_sub_iff_right]
      exact ⟨hlow.symm ▸ hsignsB.1, hhigh.symm ▸ hsignsB.2⟩
    let eta : ℝ := min c (A q - c) / 2
    have heta : 0 < eta := half_pos (lt_min hc.1 (sub_pos.mpr hc.2))
    obtain ⟨N, Q, r, tau, T, G, hQ, hQi, hQs, hr, htau,
      hG, hGheight, hGsurface, hGcore, hband⟩ :=
      ZeroChargeJoint.exists_original_sphere_collar K hK hpure hcofaces hlinks hdim
        A hAlinear hAgeneric c P hP hPi hPs hsignsc
        (hdisks c hc).1 (hdisks c hc).2.1 heta
    have hbandDisks : ∀ t ∈ Icc (-tau) tau,
        IsFinitePLBallPair (ℝ × ℝ) (disks (c + t)) (K.space ∩ {y | A y = c + t}) ∧
          disks (c + t) ⊆ {y | A y = c + t} := by
      intro t ht
      have htauMin : 2 * tau < min c (A q - c) := by
        dsimp only [eta] at htau
        linarith [htau.2]
      have hct : c + t ∈ Ioo (0 : ℝ) (A q) := by
        constructor <;> nlinarith [ht.1, ht.2, min_le_left c (A q - c),
          min_le_right c (A q - c)]
      exact ⟨(hdisks (c + t) hct).1, (hdisks (c + t) hct).2.1⟩
    obtain ⟨δ, hδ, _, hstep⟩ :=
      ZeroChargeJoint.exists_paired_step_of_original_polygon_collar hdim hCcv hKC
        A hAlinear Q hQ hQi hQs hr.1 htau.1 G hG hGheight hGsurface hGcore hband
        disks hbandDisks
    exact ⟨δ, hδ, fun u v _ _ => hstep u v⟩
  have hregions := ZeroChargeJoint.regionBalls_of_paired_steps_and_unique_extrema
    heK hhalf hhalfCv hhalfNe hdimHalf hdim J hJ hC hCcv hJC hKC A hAlinear
      (K.vertices_subset_space hp) (K.vertices_subset_space hq) hpA hqA hmin hmax
      hminfiber hmaxfiber disks (fun c hc => (hdisks c hc).1)
      (fun c hc => (hdisks c hc).2.1) hlocal
  exact hKS ▸ hregions

end PoincareConjecture.M76
