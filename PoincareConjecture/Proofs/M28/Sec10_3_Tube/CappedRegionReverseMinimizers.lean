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

theorem exists_neck_core_minimizer (T : CappedTubeCertificate g)
    (N : EpsilonNeck g) (hNU : N.carrier ⊆ T.tube.carrier)
    (hS : SmoothSphereIsotopicIn T.tube.carrier N.central_sphere
      T.tube.cylinder.middleSphere)
    (hcapN : Disjoint T.cap.carrier N.carrier)
    (hsmall : N.epsilon ≤ neckShorteningEpsilon)
    {η : ℝ → M} {a b L : ℝ} (hab : a ≤ b)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 η (Icc a b))
    (hηU : MapsTo η (Icc a b) T.carrier)
    (hη0 : η a ∈ N.central_sphere) (hη1 : η b ∈ T.cap.carrier)
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
  have hreflect : MapsTo (fun s : ℝ => 1 - s) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro s hs
    constructor <;> linarith only [hs.1, hs.2]
  have hinvolution (s : ℝ) : 1 - (1 - s) = s := by ring
  have hcross' : ∀ γ : ℝ → M, γ 0 = η a → γ 1 = η b →
      ContinuousOn γ (Icc (0 : ℝ) 1) → MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) →
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K →
        ∃ (i : Bool) (c d : ℝ), 0 ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ 1 ∧
          γ c ∈ N.central_sphere ∧ γ d ∈ N.central_sphere ∧
          γ t ∉ N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2) := by
    intro γ hγ0 hγ1 hγ hγU t ht hnot
    let rev : ℝ → M := fun s => γ (1 - s)
    have hrev : ContinuousOn rev (Icc (0 : ℝ) 1) :=
      hγ.comp
        (show Continuous (fun s : ℝ => 1 - s) from
          continuous_const.sub continuous_id).continuousOn hreflect
    have hrevU : MapsTo rev (Icc (0 : ℝ) 1) T.carrier := hγU.comp hreflect
    have hrev0 : rev 0 ∈ T.cap.carrier := by
      simpa only [rev, sub_zero, hγ1] using hη1
    have hrev1 : rev 1 ∈ N.central_sphere := by
      simpa only [rev, sub_self, hγ0] using hη0
    have hrevnot : rev (1 - t) ∉ K := by
      simpa only [rev, hinvolution] using hnot
    obtain ⟨c, d, hc, hct, htd, hd, hcs, hds, hexit⟩ :=
      hcross rev hrev0 hrev1 hrev hrevU (1 - t) (hreflect ht) hrevnot
    refine ⟨false, 1 - d, 1 - c, by linarith, by linarith, by linarith,
      by linarith, hds, hcs, ?_⟩
    simpa only [rev, hinvolution] using hexit
  obtain ⟨_, _, _, hmin⟩ :=
    exists_confined_sequence_and_minimizer_of_endpoint_crossings g U hK hKU
      (fun _ => N) (fun _ => hsmall)
      (fun _ => (N.central_sphere_subset.trans hNU).trans T.tube_subset)
      hcross' hα0 hα1 hα hαU hαL
  exact hmin

end PoincareConjecture.CappedTubeCertificate
