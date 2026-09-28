import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Rims.SpanningPaths
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.Selection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.TwoIntervalRimTraversal
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.SquareRimFilling



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem nonnull_spanning_word_of_original_rim
    {X : Type*} [TopologicalSpace X] {R : Set X}
    {T Q S K L : Set P2} (hT : IsFinitePLBallPair P2 T Q) (hQS : Q ⊆ S)
    (c : Bool → P2 → P2) (hc : ∀ i, ContinuousOn (c i) source)
    (hQ : ∀ i z, z ∈ source → (c i z ∈ Q ↔ z.1 = 0))
    (hKL : Disjoint K L)
    (hcover : (c false '' source ∪ c true '' source) ∪ (K ∪ L) = S)
    (sign : Bool → Bool)
    (hcontact : ∀ i, K ∩ (c i '' source) = c i '' arm (farArmParameter (sign i)))
    (H₀ : Sq ≃ₜ K) (hH₀ : H₀.IsFinitePL)
    (hH₀Q : ∀ z : Sq, (H₀ z : P2) ∈ Q ↔ (z : P2).2 = 0)
    (hleft₀ : ∀ t : I, (H₀ ⟨(0, t), by norm_num, t.property⟩ : P2) =
      c false (t, farArmParameter (sign false)))
    (hright₀ : ∀ t : I, (H₀ ⟨(1, t), by norm_num, t.property⟩ : P2) =
      c true (t, farArmParameter (sign true)))
    (H₁ : Sq ≃ₜ L)
    (hH₁Q : ∀ z : Sq, (H₁ z : P2) ∈ Q ↔ (z : P2).2 = 0)
    (hleft₁ : ∀ t : I, (H₁ ⟨(0, t), by norm_num, t.property⟩ : P2) =
      c false (t, farArmParameter (!(sign false))))
    (hright₁ : ∀ t : I, (H₁ ⟨(1, t), by norm_num, t.property⟩ : P2) =
      c true (t, farArmParameter (!(sign true))))
    (old : P2 → X) (hold : ContinuousOn old Q) (holdR : MapsTo old Q R)
    (rim : C(Q, R)) (hrim : ∀ z : Q, (rim z : X) = old z)
    (hnon : ¬ rim.Nullhomotopic)
    (τ : C3 → X) (hτ : ContinuousOn τ tube) (hτR : MapsTo τ tube R)
    (h0 : ∀ p ∈ source, old (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, old (c true p) = τ ((p.2, -p.2), p.1))
    (A : Path (spanningEndMap τ hτ hτR (spanningEndPoint false (sign false)))
      (spanningEndMap τ hτ hτR (spanningEndPoint true (sign true))))
    (B : Path (spanningEndMap τ hτ hτR (spanningEndPoint false (!(sign false))))
      (spanningEndMap τ hτ hτR (spanningEndPoint true (!(sign true)))))
    (hA : ∀ t : I, (A t : X) = old (H₀ ⟨(t, 0), t.property, by norm_num⟩))
    (hB : ∀ t : I, (B t : X) = old (H₁ ⟨(t, 0), t.property, by norm_num⟩)) :
    ¬ (A.trans
      (((spanningOldEndPath false (sign false)).map (spanningEndMap τ hτ hτR).continuous).trans
        (B.trans ((spanningOldEndPath true (sign true)).map
          (spanningEndMap τ hτ hτR).continuous).symm)).symm).Homotopic
            (Path.refl (spanningEndMap τ hτ hτR (spanningEndPoint false (sign false)))) := by
  obtain ⟨hab, hV, hUV, hinter, q, hq, hqval⟩ := spanning_original_rim_complement
    hT hQS c hQ hKL hcover sign hcontact H₀ hH₀ hH₀Q hleft₀ hright₀
  obtain ⟨D₀, P, D₁, hD₀, hP, hD₁, _, _, _, hpath⟩ :=
    exists_spanning_complement_paths c hc sign H₁ hH₁Q hleft₁ hright₁
  let τ' := spanningEndMap τ hτ hτR
  let E₀ := (spanningOldEndPath false (sign false)).map τ'.continuous
  let E₁ := (spanningOldEndPath true (sign true)).map τ'.continuous
  have he₀ (t : I) : (E₀ t : X) = old (D₀ t) := by
    rw [hD₀]
    exact (h0 (0, originalStripEndParameter (!(sign false)) t)
      ⟨by norm_num, originalStripEndParameter_mem _ t⟩).symm
  have he₁ (t : I) : (E₁ t : X) = old (D₁ t) := by
    rw [hD₁]
    exact (h1 (0, originalStripEndParameter (!(sign true)) t)
      ⟨by norm_num, originalStripEndParameter_mem _ t⟩).symm
  have hB' (t : I) : (B t : X) = old (P t) := (hB t).trans (congrArg old (hP t).symm)
  have hcomp (t : I) : ((E₀.trans (B.trans E₁.symm)) t : X) =
      old ((D₀.trans (P.trans D₁.symm)) t) := by
    simp only [Path.trans_apply, Path.symm_apply]
    split_ifs
    · exact he₀ _
    · exact hB' _
    · exact he₁ _
  have hq0 : (q 0 : P2) = c false (0, farArmParameter (sign false)) :=
    (hqval 0).trans (hleft₀ 0)
  have hq1 : (q 1 : P2) = c true (0, farArmParameter (sign true)) :=
    (hqval 1).trans (hright₀ 0)
  obtain ⟨J, rho, _, _, hrho, hrhohom⟩ := exists_marked_two_interval_rim_traversal
    hab hinter hUV hV q hq hq0 hq1 old hold holdR (D₀.trans (P.trans D₁.symm)) hpath
      A (E₀.trans (B.trans E₁.symm)) (fun t ↦ (hA t).trans (congrArg old (hqval t).symm)) hcomp
  intro hnull
  have hrhonull := hrhohom.trans hnull
  let gamma : C(Q2, R) := rim.comp ⟨J, J.continuous⟩
  have hvalues (t : I) : gamma (squareRimLoop t) = rho t := by
    apply Subtype.ext
    exact (hrim _).trans (hrho t).symm
  have hbase : gamma squareRimBase = τ' (spanningEndPoint false (sign false)) := by
    have hv := (hvalues 0).trans rho.source
    simpa using hv
  have hleft : (squareRimLoop.map gamma.continuous).toContinuousMap = rho.toContinuousMap :=
    ContinuousMap.ext hvalues
  have hright : (Path.refl (gamma squareRimBase)).toContinuousMap =
      (Path.refl (τ' (spanningEndPoint false (sign false)))).toContinuousMap :=
    ContinuousMap.ext (fun _ ↦ hbase)
  have hgammanull : gamma.Nullhomotopic := by
    apply nullhomotopic_of_squareRimLoop
    change (squareRimLoop.map gamma.continuous).toContinuousMap.HomotopicRel
      (Path.refl (gamma squareRimBase)).toContinuousMap {0, 1}
    rw [hleft, hright]
    exact hrhonull
  apply hnon
  have h := hgammanull.comp_left ⟨J.symm, J.symm.continuous⟩
  have he : gamma.comp ⟨J.symm, J.symm.continuous⟩ = rim := by
    apply ContinuousMap.ext
    intro z
    exact congrArg rim (J.apply_symm_apply z)
  exact he ▸ h

end PoincareConjecture.M76.Dehn
