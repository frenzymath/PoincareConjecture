import PoincareConjecture.Proofs.M47.TerminalCurvatureNegativeDiagonal
import PoincareConjecture.Proofs.M47.TerminalCurvatureFlowModulus
import PoincareConjecture.Proofs.M47.TerminalCurvatureSourceCharts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.ChartTests
import Mathlib.Data.Nat.Pairing










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance earlierJetDualNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance earlierJetDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance earlierJetBilinearNormedAddCommGroup :
    NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance earlierJetBilinearNormedSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace



theorem terminalCurvature_exists_earlier_source_jets
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace E (M k)] [∀ k, IsManifold (𝓡 3) ∞ (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    (tau : ℕ → ℝ) (htau : ∀ k, 0 < tau k)
    (F : ∀ k, RicciFlow 3 (M k) (Icc (-tau k) 0))
    (g : RiemannianMetric 3 X)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : (⋃ k, U k) = univ)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (M k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hjet : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (((F k).metric 0).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K) :
    ∃ s : ℕ → ℝ, (∀ k, s k ∈ Ioo (-tau k) 0) ∧ Tendsto s atTop (𝓝 0) ∧
      ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m
          (((F k).metric (s k)).pullbackCoefficients (phi k ∘ (c i).symm)))
        (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K := by
  classical
  choose K hK hKtarget _hKmono hcofinal using fun i =>
    exists_compact_tests_of_isOpen (c i).open_target
  let chart (n : ℕ) := (Nat.unpair n).1
  let buffer (n : ℕ) := (Nat.unpair (Nat.unpair n).2).1
  let order (n : ℕ) := (Nat.unpair (Nat.unpair n).2).2
  let tests (n : ℕ) : Set E := K (chart n) (buffer n)
  let Y (n : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin (order n) => E) Bilin
  let d (k n : ℕ) := (phi k).symm.trans (c (chart n))
  let Available (k n : ℕ) : Prop := tests n ⊆ (d k n).target
  let f (k n : ℕ) (s : ℝ) (x : E) : Y n := iteratedFDeriv ℝ (order n)
    (((F k).metric s).pullbackCoefficients (phi k ∘ (c (chart n)).symm)) x
  let limit (n : ℕ) (x : E) : Y n := iteratedFDeriv ℝ (order n)
    (g.pullbackCoefficients (c (chart n)).symm) x
  have hAvailable (n : ℕ) : ∀ᶠ k in atTop, Available k n :=
    (terminalCurvature_source_chart_readout U hU hmono hcover phi hsource (c (chart n))
      (hK (chart n) (buffer n)) (hKtarget (chart n) (buffer n))).2
  have hlimit (n : ℕ) : TendstoUniformlyOn (fun k => f k n 0) (limit n) atTop (tests n) :=
    hjet (chart n) (order n) _ (hK (chart n) (buffer n)) (hKtarget (chart n) (buffer n))
  have hmod (k n : ℕ) (havailable : Available k n) (rho : ℝ) (hrho : 0 < rho) :
      ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ Icc (-tau k) 0, |s| < delta →
        ∀ x ∈ tests n, dist (f k n s x) (f k n 0 x) < rho := by
    obtain ⟨delta, hdelta, htime⟩ := terminalCurvature_metric_time_modulus
      (neg_neg_of_pos (htau k)) (F k) (d k n).open_target (d k n).symm
      (d k n).contMDiffOn_invFun (hK (chart n) (buffer n)) havailable (order n) hrho
    refine ⟨delta, hdelta, ?_⟩
    intro s hs hsmall x hx
    have hzero : (0 : ℝ) ∈ Icc (-tau k) 0 := ⟨by linarith [htau k], le_rfl⟩
    have h := htime s hs 0 hzero (by simpa only [sub_zero] using hsmall)
      x hx (order n) le_rfl
    have he := (d k n).contMDiffOn_invFun.contMDiffAt
      ((d k n).open_target.mem_nhds (havailable hx))
    have hnew := ((F k).metric s).contDiffAt_pullbackCoefficients he
    have hold := ((F k).metric 0).contDiffAt_pullbackCoefficients he
    change ContDiffAt ℝ ∞ (((F k).metric s).pullbackCoefficients (d k n).symm) x at hnew
    change ContDiffAt ℝ ∞ (((F k).metric 0).pullbackCoefficients (d k n).symm) x at hold
    change ‖iteratedFDeriv ℝ (order n)
      (((F k).metric s).pullbackCoefficients (d k n).symm -
        ((F k).metric 0).pullbackCoefficients (d k n).symm) x‖ < rho at h
    rw [iteratedFDeriv_sub_apply (i := order n) (hnew.of_le (by exact_mod_cast le_top))
      (hold.of_le (by exact_mod_cast le_top))] at h
    exact (show dist (f k n s x) (f k n 0 x) =
      ‖iteratedFDeriv ℝ (order n) (((F k).metric s).pullbackCoefficients (d k n).symm) x -
        iteratedFDeriv ℝ (order n) (((F k).metric 0).pullbackCoefficients (d k n).symm) x‖
        from dist_eq_norm _ _).symm ▸ h
  obtain ⟨s, hs, hszero, hrows⟩ := terminalCurvature_negative_diagonal_uniform_limit
    tests tau htau Available hAvailable f limit hlimit hmod
  refine ⟨s, hs, hszero, ?_⟩
  intro i m A hA hAtarget
  obtain ⟨j, hj⟩ := hcofinal i A hA hAtarget
  have hrow := hrows (Nat.pair i (Nat.pair j m))
  dsimp (config := { instances := true }) only [f, limit, tests, Y] at hrow
  rw [show order (Nat.pair i (Nat.pair j m)) = m by simp [order],
    show chart (Nat.pair i (Nat.pair j m)) = i by simp [chart],
    show buffer (Nat.pair i (Nat.pair j m)) = j by simp [buffer]] at hrow
  have hfull : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (((F k).metric (s k)).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop (K i j) := by
    exact hrow
  exact hfull.mono hj

end PoincareConjecture.M47
