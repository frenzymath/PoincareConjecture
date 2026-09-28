import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CapTubeOverlapChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CapStandardEnd










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D




theorem capTubeAttachment_exists_standardOverlapEnd_of_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    {X : Set M} {C : CapCertificate g}
    {T : EpsilonTubeCertificate g X} {side : Bool}
    (A : CapTubeAttachment C T side)
    (hkind : C.model_kind = CapModelKind.euclidean) :
    let U : TopologicalSpace.Opens M :=
      ⟨C.carrier, C.carrier_open⟩
    ∃ omega : Bool, ∀ v ∈ Ioo (0 : ℝ) 1,
      ∃ (Phi : Diffeomorph (𝓡 3) (𝓡 3) U E3 ∞)
        (R : E3 ≃ₗᵢ[ℝ] E3) (r0 : ℝ)
        (sigma : OpenPartialHomeomorph ℝ ℝ),
        0 < r0 ∧ sigma.source = Ioo v 1 ∧ sigma.target = Ioi r0 ∧
        ContDiffOn ℝ ∞ (sigma : ℝ → ℝ) sigma.source ∧
        ContDiffOn ℝ ∞ sigma.symm sigma.target ∧
        StrictMonoOn (sigma : ℝ → ℝ) sigma.source ∧
        (∀ s ∈ sigma.source, 0 < deriv (sigma : ℝ → ℝ) s) ∧
        (∀ (q : UnitTwoSphere) (s : ℝ) (x : U),
          s ∈ Ioo v 1 →
          x.val = A.overlap_model.coordinate
            (q, if omega then s else 1 - s) →
          Phi x = sigma s • (sphereMap R q).val) := by
  classical
  let U : TopologicalSpace.Opens M := ⟨C.carrier, C.carrier_open⟩
  change ∃ omega : Bool, ∀ v ∈ Ioo (0 : ℝ) 1,
    ∃ (Phi : Diffeomorph (𝓡 3) (𝓡 3) U E3 ∞), _
  obtain ⟨omega, e, hsource, _, hforward, _, he, hei, _, hend⟩ :=
    capTubeAttachment_exists_cofinalOverlapChart A
  refine ⟨omega, ?_⟩
  intro v hv
  let R := C.model_equivalence
  let : TopologicalSpace R.model := R.model_topology
  let : ChartedSpace E3 R.model := R.model_charted
  let : IsManifold (𝓡 3) ∞ R.model := R.model_manifold
  obtain ⟨F, _, _⟩ := capModelEquivalence_exists_carrierDiffeomorph U R
  have hstd : Nonempty (Diffeomorph (𝓡 3) (𝓡 3) R.model E3 ∞) := by
    have h := R.standard_smooth
    split at h
    · exact h
    · simp_all only [reduceCtorEq]
  obtain ⟨D0⟩ := hstd
  let Phi0 := F.trans D0
  have hc : v / 2 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hv.1, hv.2]
  have heta : 0 < v / 2 := half_pos hv.1
  have hcv : v / 2 + v / 2 = v := by ring
  have hcb : v / 2 + v / 2 < 1 := by rw [hcv]; exact hv.2
  obtain ⟨Phi, R0, r0, sigma, hr0, hsrc, htgt, hs, hsi, hmono, hderiv, hformula⟩ :=
    standardEnd_of_openPartialHomeomorph hS hD Phi0 e hsource he hei hend hc heta hcb
  rw [hcv] at hsrc hformula
  refine ⟨Phi, R0, r0, sigma, hr0, hsrc, htgt, hs, hsi, hmono, hderiv, ?_⟩
  intro q s x hs hx
  have hzs : (q, s) ∈ e.source := by
    rw [hsource]
    exact ⟨mem_univ _, hv.1.trans hs.1, hs.2⟩
  have hex : e (q, s) = x := Subtype.ext ((hforward (q, s) hzs).trans hx.symm)
  simpa only [hex] using hformula q s hs

end PoincareConjecture.M25.Topology3D
