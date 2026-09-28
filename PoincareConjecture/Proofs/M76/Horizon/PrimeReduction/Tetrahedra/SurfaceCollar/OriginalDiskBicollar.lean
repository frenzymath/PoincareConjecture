import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.OriginalSphereBicollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : P2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem ChartwisePLSphere.exists_original_disk_bicollar
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S U : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U)
    (j : P2 → X) (hj : PolyhedralPLInCharts e j D)
    (hji : InjOn j D) (hjS : MapsTo j D S) :
    ∃ b : P2 × ℝ → X,
      PolyhedralPLInCharts e b (D ×ˢ I) ∧ InjOn b (D ×ˢ I) ∧
      MapsTo b (D ×ˢ I) (U ∩ interior R) ∧
      (∀ x ∈ D, b (x, 0) = j x) ∧
      (∀ z ∈ D ×ˢ I, b z ∈ S ↔ z.2 = 0) ∧
      Nonempty (ChartwisePLBall e (b '' (D ×ˢ I))
        (b '' ((sphere (0 : P2) 1 ×ˢ I) ∪ (D ×ˢ {-1, 1})))) ∧
      interior (b '' (D ×ˢ I)) = b '' (ball (0 : P2) 1 ×ˢ Ioo (-1) 1) := by
  classical
  obtain ⟨t, F, N, HB, c, _, _, _, _, hN, hc, hci, _, hc0, hcS,
    δ, hδ, hδsmall, hthin, _⟩ :=
    s.exists_original_small_bicollar_with_model hR he hSR hU hSU
  let E := t → ℝ × V3
  have hci' : InjOn c (N.space ×ˢ I) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hci.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  let q : P2 → E := fun x => if hx : x ∈ D then HB.symm ⟨j x,hjS hx⟩ else 0
  have hqval (x : D) : q x = (HB.symm ⟨j x,hjS x.property⟩ : E) := by
    simp only [q,dif_pos x.property]
  have hqN : MapsTo q D N.space := by
    intro x hx
    rw [hqval ⟨x,hx⟩]
    exact (HB.symm ⟨j x,hjS hx⟩).property
  have hqcont : ContinuousOn q D := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (HB.symm.continuous.comp
      (hj.continuousOn.domRestrict.subtype_mk (fun x => hjS x.property)))
    convert h using 1
    funext x
    exact hqval x
  have hqbase (x : P2) (hx : x ∈ D) : c (q x,0) = j x := by
    rw [hqval ⟨x,hx⟩,hc0,HB.apply_symm_apply]
  let A : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hA : FinitePiecewiseAffineOn A N.space := ⟨N,hN,rfl,N.affineOnFaces_affine A⟩
  have hslice : PolyhedralPLInCharts e (fun x => c (x,0)) N.space :=
    hc.comp_finitePiecewiseAffineOn N hN hA (fun x hx => ⟨hx,by norm_num⟩)
  have hslicei : InjOn (fun x => c (x,0)) N.space := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (hci' ⟨hx,by norm_num⟩ ⟨hy,by norm_num⟩ hxy)
  have hD : IsFinitePLBallPair P2 D (sphere (0 : P2) 1) := by
    have h := CoordinateHalfBoxes.base_ballPair (by norm_num : (0 : ℝ) < 1)
    have hbase : CoordinateHalfBoxes.base 1 = D := by
      ext x
      simp only [CoordinateHalfBoxes.base,mem_prod,mem_Icc,mem_closedBall,
        dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
    have hfront := h.frontier_eq_of_finrank_eq rfl
    rw [hbase,frontier_closedBall _ one_ne_zero] at hfront
    rwa [hbase,← hfront] at h
  obtain ⟨K,_,hK,hKD,_,_⟩ := hD.exists_finite_carrier_and_rim_complexes
  have hq : FinitePiecewiseAffineOn q D := by
    have hcomp : PolyhedralPLInCharts e ((fun x => c (x,0)) ∘ q) D :=
      hj.congr (fun x hx => (hqbase x hx).symm)
    exact hKD ▸ hslice.finitePiecewiseAffineOn_lift he.compatible hslicei K hK
      (hqcont.mono hKD.subset) (fun _ hx => hqN (hKD.subset hx)) (hKD.symm ▸ hcomp)
  have hqi : InjOn q D := by
    intro x hx y hy hxy
    apply hji hx hy
    rw [← hqbase x hx,← hqbase y hy,hxy]
  let T : ℝ →ᴬ[ℝ] ℝ := δ • ContinuousAffineMap.id ℝ ℝ
  have hTval (u : ℝ) : T u = δ * u := rfl
  have hI := isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)
  obtain ⟨J,_,hJ,hJI,_,_⟩ := hI.exists_finite_carrier_and_rim_complexes
  have hT : FinitePiecewiseAffineOn T I := ⟨J,hJ,hJI,J.affineOnFaces_affine T⟩
  let G := Prod.map q T
  have hG : FinitePiecewiseAffineOn G (D ×ˢ I) := hq.prodMap hT
  have hTthin (u : ℝ) (hu : u ∈ I) : T u ∈ Icc (-δ) δ := by
    rw [hTval]
    constructor <;> nlinarith [hu.1,hu.2]
  have hGfull (z : P2 × ℝ) (hz : z ∈ D ×ˢ I) : G z ∈ N.space ×ˢ I := by
    refine ⟨hqN hz.1,?_,?_⟩
    · change -1 ≤ T z.2
      linarith [(hTthin z.2 hz.2).1]
    · change T z.2 ≤ 1
      linarith [(hTthin z.2 hz.2).2]
  let b := c ∘ G
  have hb : PolyhedralPLInCharts e b (D ×ˢ I) := by
    obtain ⟨L,hL,hLs,hfaces⟩ := hG
    rw [← hLs]
    exact hc.comp_finitePiecewiseAffineOn L hL ⟨L,hL,rfl,hfaces⟩
      (fun z hz => hGfull z (hLs.subset hz))
  have hbi : InjOn b (D ×ˢ I) := by
    intro x hx y hy hxy
    have heq := hci' (hGfull x hx) (hGfull y hy) hxy
    apply Prod.ext
    · exact hqi hx.1 hy.1 (congrArg Prod.fst heq)
    · exact mul_left_cancel₀ hδ.ne' (congrArg Prod.snd heq)
  have hball := hD.prod hI
  have hv : (P2 × ℝ) ≃L[ℝ] V3 :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := P2 × ℝ) (F := V3)
      (by simp [Module.finrank_prod])
  obtain ⟨bball⟩ := exists_chartwisePLBall_image hball hv hb subset_rfl hbi
  refine ⟨b,hb,hbi,?_,?_,?_,⟨bball⟩,?_⟩
  · intro z hz
    exact hthin ⟨hqN hz.1,hTthin z.2 hz.2⟩
  · intro x hx
    change c (q x,δ * 0) = j x
    simpa using hqbase x hx
  · intro z hz
    exact (hcS ⟨G z,hGfull z hz⟩).trans (mul_eq_zero.trans (or_iff_right hδ.ne'))
  · rw [bball.interior_eq_sdiff,← hbi.image_sdiff_subset hball.1]
    congr 1
    rw [← hball.interior_eq_sdiff_of_finrank_eq rfl,interior_prod_eq,
      interior_closedBall _ one_ne_zero,interior_Icc]

end PoincareConjecture.M76
