import PoincareConjecture.Proofs.M28.Sec10_3_Tube.TubeNeckConfinement
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.ConfinementMinimizers










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.EpsilonTubeCertificate

open M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} {X : Set M}



theorem exists_chain_neck_minimizer (T : EpsilonTubeCertificate g X)
    (i j : ℤ) (hi : i ∈ T.chain.shape.active) (hj : j ∈ T.chain.shape.active)
    (hdisj : Disjoint (T.chain.neck i).carrier (T.chain.neck j).carrier)
    (hsmall : T.epsilon ≤ neckShorteningEpsilon)
    {η : ℝ → M} {a b L : ℝ} (hab : a ≤ b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a b))
    (hηU : MapsTo η (Icc a b) T.carrier)
    (hη0 : η a ∈ (T.chain.neck i).central_sphere)
    (hη1 : η b ∈ (T.chain.neck j).central_sphere)
    (hηL : g.pathELength η a b < ENNReal.ofReal L) :
    ∃ γ : ℝ → M, γ 0 = η a ∧ γ 1 = η b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) T.carrier ∧
      g.pathELength γ 0 1 = intrinsicEDist g T.carrier (η a) (η b) ∧
      g.pathELength γ 0 1 ≠ ⊤ ∧ g.pathELength γ 0 1 < ENNReal.ofReal L := by
  let N : Bool → EpsilonNeck g := fun k => T.chain.neck (if k then j else i)
  have hactive (k : Bool) : (if k then j else i) ∈ T.chain.shape.active := by
    cases k
    · exact hi
    · exact hj
  have hNsmall (k : Bool) : (N k).epsilon ≤ neckShorteningEpsilon := by
    exact (T.chain.epsilon_eq _ (hactive k)).trans_le hsmall
  have hNU (k : Bool) : (N k).carrier ⊆ T.carrier := by
    rw [T.carrier_eq_chain_union]
    exact subset_iUnion_of_subset ⟨_, hactive k⟩ Subset.rfl
  obtain ⟨K, hK, hKU, hcross⟩ := T.exists_chain_neck_confinement i j hi hj hdisj
  let U : TopologicalSpace.Opens M := ⟨T.carrier, T.carrier_open⟩
  obtain ⟨α, hα0, hα1, hα, hαU, hαlength⟩ := exists_unit_interval_path g hab hη hηU
  have hαL : g.pathELength α 0 1 < ENNReal.ofReal L := hαlength ▸ hηL
  have hcross' : ∀ γ : ℝ → M, γ 0 = η a → γ 1 = η b →
      ContinuousOn γ (Icc (0 : ℝ) 1) → MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) →
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K →
        ∃ (k : Bool) (c d : ℝ), 0 ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ 1 ∧
          γ c ∈ (N k).central_sphere ∧ γ d ∈ (N k).central_sphere ∧
          γ t ∉ (N k).region (-((N k).epsilon⁻¹ / 2)) ((N k).epsilon⁻¹ / 2) := by
    intro γ hγ0 hγ1 hγ hγU t ht hnot
    exact hcross γ (hγ0 ▸ hη0) (hγ1 ▸ hη1) hγ hγU t ht hnot
  obtain ⟨_, _, _, hmin⟩ :=
    exists_confined_sequence_and_minimizer_of_endpoint_crossings g U hK hKU N hNsmall
      (fun k => (N k).central_sphere_subset.trans (hNU k))
      hcross' hα0 hα1 hα hαU hαL
  exact hmin

end PoincareConjecture.EpsilonTubeCertificate
