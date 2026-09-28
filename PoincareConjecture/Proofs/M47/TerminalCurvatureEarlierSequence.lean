import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierJets
import PoincareConjecture.Proofs.M47.TerminalCurvatureEarlierPhysical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_exists_earlier_physical_sequence
    (S : ℕ → SurgeryFlowData.{u}) (C : ℕ → GeneralizedSliceCarrier.{u})
    (b Q tau : ℕ → ℝ) (htau : ∀ k, 0 < tau k)
    (V : ∀ k, TopologicalSpace.Opens (C k).carrier) (q : ∀ k, V k)
    (e : ∀ k, SurgeryFlowCylinder (S k) (C k) (b k) (Q k) (Icc (-tau k) 0) (V k))
    (F : ∀ k, RicciFlow 3 (V k) (Icc (-tau k) 0))
    (hmetric : ∀ k (s : ℝ) (hs : s ∈ Icc (-tau k) 0) (y : V k)
      (v w : TangentSpace (𝓡 3) y),
      ((F k).metric s).inner y v w = (e k).pullbackInner s hs y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V k → (C k).carrier) y v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V k → (C k).carrier) y w))
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X)
    (U : ℕ → Set X) (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (hcover : (⋃ k, U k) = univ)
    (phi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) X (V k) ∞)
    (hsource : ∀ k, (phi k).source = U k)
    (c : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞)
    (hjet : ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (((F k).metric 0).pullbackCoefficients (phi k ∘ (c i).symm)))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K) :
    ∃ s : ℕ → ℝ, ∃ hs : ∀ k, s k ∈ Ioo (-tau k) 0,
      Tendsto s atTop (𝓝 0) ∧
      (∀ k, b k + s k / Q k ∈ Ico 0 (b k) ∧
        b k + s k / Q k ∈ (S k).time_domain) ∧
      ∃ psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3)
          X ((S k).slice (b k + s k / Q k)).carrier ∞,
        (∀ k, (psi k).source = U k) ∧
        (∀ k x, psi k x = (e k).forward (s k) ⟨(hs k).1.le, (hs k).2.le⟩ (phi k x).val) ∧
        ∀ i m K, IsCompact K → K ⊆ (c i).target → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m
            ((rescaledMetric ((S k).metric (b k + s k / Q k)) (Q k)
              (e k).scale_pos).pullbackCoefficients (psi k ∘ (c i).symm)))
          (iteratedFDeriv ℝ m (g.pullbackCoefficients (c i).symm)) atTop K := by
  classical
  obtain ⟨s, hs, hs0, hjets⟩ := terminalCurvature_exists_earlier_source_jets
    tau htau F g U hU hmono hcover phi hsource c hjet
  have hscc (k : ℕ) : s k ∈ Icc (-tau k) 0 := ⟨(hs k).1.le, (hs k).2.le⟩
  choose chi hchi_source hchi_forward hchi_metric using fun k =>
    terminalCurvature_exists_physical_slice_chart (V k) (e k) (s k) (hscc k)
      (q k) ((F k).metric (s k)) (hmetric k (s k) (hscc k))
  let psi (k : ℕ) := (phi k).trans (chi k)
  have hpsi_source (k : ℕ) : (psi k).source = U k :=
    (terminalCurvature_physical_composite_source (phi k) (chi k) (hchi_source k)).trans
      (hsource k)
  refine ⟨s, hs, hs0, ?_, psi, hpsi_source, ?_, ?_⟩
  · intro k
    have hdomain : b k + s k / Q k ∈ (S k).time_domain :=
      (e k).time_subset (mem_image_of_mem _ (hscc k))
    have hnegative : s k / Q k < 0 := div_neg_of_neg_of_pos (hs k).2 (e k).scale_pos
    exact ⟨⟨(S k).time_domain_nonnegative hdomain, by linarith⟩, hdomain⟩
  · intro k x
    exact hchi_forward k (phi k x)
  · intro i m K hK hKtarget
    have havailable := (terminalCurvature_source_chart_readout U hU hmono hcover phi
      hsource (c i) hK hKtarget).2
    apply (hjets i m K hK hKtarget).congr
    filter_upwards [havailable] with k hk x hx
    exact (terminalCurvature_physical_composite_jets ((F k).metric (s k))
      (rescaledMetric ((S k).metric (b k + s k / Q k)) (Q k) (e k).scale_pos)
      (phi k) (chi k) (hchi_source k) (hchi_metric k) (c i) m (hk hx)).symm

end PoincareConjecture.M47
