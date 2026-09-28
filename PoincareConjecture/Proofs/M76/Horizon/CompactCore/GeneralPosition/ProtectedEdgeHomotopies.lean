import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.ProtectedVertexMotion
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.GeneralPosition.FiniteChartEdgeControl
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleNormalCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals











set_option autoImplicit false

open Set Metric Geometry unitInterval

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_protected_edge_homotopies
    {X ι κ ν : Type*} [TopologicalSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (B : κ → OpenPartialHomeomorph X V3) (src dst : κ → ν) (f : ν → X)
    (hcompat : ∀ k i, (e i).symm.trans (B k) ∈ piecewiseAffineGroupoid V3)
    (hfY : ∀ v, f v ∈ Y) (U : κ → Set X) (hU : ∀ k, IsOpen (U k))
    (hsrc : ∀ k, f (src k) ∈ (B k).source)
    (hdst : ∀ k, f (dst k) ∈ (B k).source)
    (hedge : ∀ k, segment ℝ (B k (f (src k))) (B k (f (dst k))) ⊆
      (B k).target ∩ (B k).symm ⁻¹' U k) :
    ∃ (p : ν → C(I, X)) (H : κ → C(I × I, X)),
      (∀ v, p v 0 = f v) ∧ (∀ v t, p v t ∈ Y) ∧
      (∀ v, f v ∉ F → ∀ t, p v t = f v) ∧
      (∀ v (t : I), 0 < (t : ℝ) → p v t ∉ F) ∧
      (∀ k z, H k z ∈ U k) ∧
      (∀ k t, H k (t, 0) = p (src k) t ∧ H k (t, 1) = p (dst k) t) ∧
      (∀ k t s, H k (t, s) = (B k).symm
        (AffineMap.lineMap (B k (p (src k) t)) (B k (p (dst k) t)) (s : ℝ))) ∧
      (∀ k t s, B k (H k (t, s)) =
        AffineMap.lineMap (B k (p (src k) t)) (B k (p (dst k) t)) (s : ℝ)) ∧
      (∀ k, PolyhedralPLInCharts e
        ((B k).symm ∘ AffineMap.lineMap (B k (p (src k) 1)) (B k (p (dst k) 1)))
        (Icc (0 : ℝ) 1)) ∧
      ∀ k s, H k (0, s) = (B k).symm
        (AffineMap.lineMap (B k (f (src k))) (B k (f (dst k))) (s : ℝ)) := by
  classical
  obtain ⟨O, V, hO, hV, hcontrol⟩ :=
    OpenPartialHomeomorph.exists_finite_edge_control B src dst f U hU hsrc hdst hedge
  choose p hp0 hpO hpfix hpoff using fun v =>
    hN.exists_protected_vertex_motion hY hcut (hO v).1 (hfY v) (hO v).2
  have hctrl (t : I) (k : κ) := hcontrol (fun v => p v t) (fun v => (hpO v t).1) k
  let A : κ → I × I → V3 := fun k z =>
    AffineMap.lineMap (B k (p (src k) z.1)) (B k (p (dst k) z.1)) (z.2 : ℝ)
  have hAV (k : κ) (z : I × I) : A k z ∈ V k :=
    (hctrl z.1 k).2.2 (lineMap_mem_segment ℝ _ _ z.2.property)
  have hAc (k : κ) : Continuous (A k) := by
    have hl : Continuous (fun z : I × I => B k (p (src k) z.1)) :=
      (B k).continuousOn.comp_continuous ((p (src k)).continuous.comp continuous_fst)
        (fun z => (hctrl z.1 k).1)
    have hr : Continuous (fun z : I × I => B k (p (dst k) z.1)) :=
      (B k).continuousOn.comp_continuous ((p (dst k)).continuous.comp continuous_fst)
        (fun z => (hctrl z.1 k).2.1)
    simp only [A, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    exact ((continuous_subtype_val.comp continuous_snd).smul (hr.sub hl)).add hl
  let H : κ → C(I × I, X) := fun k => ⟨(B k).symm ∘ A k,
    (B k).symm.continuousOn.comp_continuous (hAc k)
      (fun z => (hV k).2.2.1 (hAV k z))⟩
  refine ⟨p, H, hp0, fun v t => (hpO v t).2, hpfix, hpoff,
    fun k z => (hV k).2.2.2 (hAV k z), ?_, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro k t
    constructor
    · change (B k).symm (AffineMap.lineMap _ _ (0 : ℝ)) = _
      rw [AffineMap.lineMap_apply_zero, (B k).left_inv (hctrl t k).1]
    · change (B k).symm (AffineMap.lineMap _ _ (1 : ℝ)) = _
      rw [AffineMap.lineMap_apply_one, (B k).left_inv (hctrl t k).2.1]
  · intro k t s
    exact (B k).right_inv ((hV k).2.2.1 (hAV k (t, s)))
  · intro k
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
    let L : ℝ →ᴬ[ℝ] V3 :=
      ContinuousAffineMap.lineMap (B k (p (src k) 1)) (B k (p (dst k) 1))
    have hL := (K.affineOnFaces_affine L).finitePiecewiseAffineOn hK
    have hmap : MapsTo L K.space (B k).target := by
      intro s hs
      have hsI : s ∈ I := by change s ∈ Icc (0 : ℝ) 1; rwa [← hKI]
      exact (hV k).2.2.1 (hAV k (1, ⟨s, hsI⟩))
    have hPL := polyhedralPLInCharts_of_compatible_inverse e (B k)
      (fun x _ => hN.cover x) (hcompat k) K hK hL hmap
    simpa only [L, ContinuousAffineMap.coe_lineMap_eq, hKI] using hPL
  · intro k s
    change (B k).symm (AffineMap.lineMap _ _ (s : ℝ)) = _
    rw [hp0, hp0]

end PoincareConjecture.M76
