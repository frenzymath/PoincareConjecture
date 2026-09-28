import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapNeckConfinement
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.ConfinementMinimizers

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.CappedTubeCertificate

open M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem exists_core_neck_minimizer (T : CappedTubeCertificate g)
    (N : EpsilonNeck g) (hNU : N.carrier ⊆ T.tube.carrier)
    (hS : SmoothSphereIsotopicIn T.tube.carrier N.central_sphere
      T.tube.cylinder.middleSphere)
    (hcapN : Disjoint T.cap.carrier N.carrier)
    (hsmall : N.epsilon ≤ neckShorteningEpsilon)
    {η : ℝ → M} {a b L : ℝ} (hab : a ≤ b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a b))
    (hηU : MapsTo η (Icc a b) T.carrier)
    (hη0 : η a ∈ T.cap.carrier) (hη1 : η b ∈ N.central_sphere)
    (hηL : g.pathELength η a b < ENNReal.ofReal L) :
    ∃ γ : ℝ → M, γ 0 = η a ∧ γ 1 = η b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) T.carrier ∧
      g.pathELength γ 0 1 = intrinsicEDist g T.carrier (η a) (η b) ∧
      g.pathELength γ 0 1 ≠ ⊤ ∧ g.pathELength γ 0 1 < ENNReal.ofReal L := by
  obtain ⟨K, hK, hKU, hcross⟩ := T.exists_core_neck_confinement N hNU hS hcapN
  have hopen : IsOpen T.carrier := by
    rw [T.carrier_eq_union]
    exact T.cap.carrier_open.union T.tube.carrier_open
  let U : TopologicalSpace.Opens M := ⟨T.carrier, hopen⟩
  obtain ⟨α, hα0, hα1, hα, hαU, hαlength⟩ := exists_unit_interval_path g hab hη hηU
  have hαL : g.pathELength α 0 1 < ENNReal.ofReal L := hαlength ▸ hηL
  have hcross' : ∀ γ : ℝ → M, γ 0 = η a → γ 1 = η b →
      ContinuousOn γ (Icc (0 : ℝ) 1) → MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) →
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K →
        ∃ (i : Bool) (c d : ℝ), 0 ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ 1 ∧
          γ c ∈ N.central_sphere ∧ γ d ∈ N.central_sphere ∧
          γ t ∉ N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2) := by
    intro γ hγ0 hγ1 hγ hγU t ht hnot
    obtain ⟨c, d, hc, hct, htd, hd, hcs, hds, hexit⟩ :=
      hcross γ (hγ0 ▸ hη0) (hγ1 ▸ hη1) hγ hγU t ht hnot
    exact ⟨false, c, d, hc, hct, htd, hd, hcs, hds, hexit⟩
  obtain ⟨_, _, _, hmin⟩ :=
    exists_confined_sequence_and_minimizer_of_endpoint_crossings g U hK hKU
      (fun _ => N) (fun _ => hsmall)
      (fun _ => (N.central_sphere_subset.trans hNU).trans T.tube_subset)
      hcross' hα0 hα1 hα hαU hαL
  exact hmin

end PoincareConjecture.CappedTubeCertificate
