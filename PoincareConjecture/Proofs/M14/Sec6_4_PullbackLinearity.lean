import PoincareConjecture.Proofs.M14.Sec6_2_PullbackReparametrization
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackCongruence











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J : Set ℝ} {Y Z H : ∀ s, G.Horizontal (γ s)}




noncomputable def affinePullbackExtension (EY : M14PullbackExtension G γ J Y)
    (EZ : M14PullbackExtension G γ J Z) (c : ℝ) :
    M14PullbackExtension G γ J (fun s => Y s + c • Z s) := by
  let W : ℝ → HorizontalSection G.spacetime := fun s q =>
    EY.extension s q + c • EZ.extension s q
  let U := EY.joint_smooth.choose ∩ EZ.joint_smooth.choose
  have hU : IsOpen U := EY.joint_smooth.choose_spec.1.inter EZ.joint_smooth.choose_spec.1
  have hgraph (s : ℝ) (hs : s ∈ J) : (s, γ s) ∈ U :=
    ⟨EY.joint_smooth.choose_spec.2.1 s hs, EZ.joint_smooth.choose_spec.2.1 s hs⟩
  let base : ContMDiffMap ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (spacetimeModel n) (ℝ × G.Point) G.Point ∞ := ⟨Prod.snd, contMDiff_snd⟩
  let : ∀ z, AddCommGroup (((base : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) z) :=
    fun z => inferInstanceAs (AddCommGroup (G.Horizontal (base z)))
  let : ∀ z, Module ℝ (((base : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) z) :=
    fun z => inferInstanceAs (Module ℝ (G.Horizontal (base z)))
  let A : ∀ z, ((base : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) z :=
    fun z => EY.extension z.1 z.2
  let B : ∀ z, ((base : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) z :=
    fun z => EZ.extension z.1 z.2
  have hA : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (((𝓘(ℝ, ℝ)).prod (spacetimeModel n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) z (A z)) U := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_pullback_section_iff base A U z).mpr
      ((EY.joint_smooth.choose_spec.2.2 z hz.1).mono inter_subset_left)
  have hB : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (((𝓘(ℝ, ℝ)).prod (spacetimeModel n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) z (B z)) U := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_pullback_section_iff base B U z).mpr
      ((EZ.joint_smooth.choose_spec.2.2 z hz.2).mono inter_subset_right)
  have hsum := hA.add_section (hB.const_smul_section (a := c))
  have hW : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) z.2 (W z.1 z.2)) U := by
    intro z hz
    exact (Bundle.contMDiffWithinAt_pullback_section_iff base
      (fun z => A z + c • B z) U z).mp (hsum z hz)
  refine {
    extension := W
    domain := EY.domain ∩ EZ.domain
    domain_open := EY.domain_open.inter EZ.domain_open
    graph_mem := fun s hs => ⟨EY.graph_mem s hs, EZ.graph_mem s hs⟩
    spatial_smooth := ?_
    joint_smooth := ⟨U, hU, hgraph, hW⟩
    agrees := ?_
    parameter_derivative := ?_ }
  · intro s
    exact ((EY.spatial_smooth s).mono inter_subset_left).add_section
      (((EZ.spatial_smooth s).mono inter_subset_right).const_smul_section)
  · intro s hs
    dsimp only [W]
    rw [EY.agrees s hs, EZ.agrees s hs]
  · intro s hs
    exact horizontal_parameter_hasDerivAt_of_contMDiffAt W s (γ s)
      ((hW _ (hgraph s hs)).contMDiffAt (hU.mem_nhds (hgraph s hs)))




theorem horizontalCovariantDerivative_affine
    (EY : M14PullbackExtension G γ J Y) (EZ : M14PullbackExtension G γ J Z) (c : ℝ)
    {s : ℝ} (hs : s ∈ J) :
    M14HorizontalCovariantDerivative G γ J (fun r => Y r + c • Z r)
        (affinePullbackExtension EY EZ c) s =
      M14HorizontalCovariantDerivative G γ J Y EY s +
        c • M14HorizontalCovariantDerivative G γ J Z EZ s := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal (γ s)) :=
    (metric.toCore (γ s)).toNormedAddCommGroupOfTopology
      (metric.continuousAt (γ s)) (metric.isVonNBounded (γ s))
  let : InnerProductSpace ℝ (G.Horizontal (γ s)) :=
    .ofCoreOfTopology (metric.toCore (γ s))
      (metric.continuousAt (γ s)) (metric.isVonNBounded (γ s))
  obtain ⟨dY, hdY⟩ := EY.parameter_derivative s hs
  obtain ⟨dZ, hdZ⟩ := EZ.parameter_derivative s hs
  have hd := (hdY.differentiableAt.hasDerivAt.add
    (hdZ.differentiableAt.hasDerivAt.const_smul c)).deriv
  change deriv (fun r => EY.extension r (γ s) + c • EZ.extension r (γ s)) s =
    deriv (fun r => EY.extension r (γ s)) s + c • deriv (fun r => EZ.extension r (γ s)) s at hd
  have hY := ((EY.spatial_smooth s _ (EY.graph_mem s hs)).contMDiffAt
    (EY.domain_open.mem_nhds (EY.graph_mem s hs))).mdifferentiableAt (by simp)
  have hZ := ((EZ.spatial_smooth s _ (EZ.graph_mem s hs)).contMDiffAt
    (EZ.domain_open.mem_nhds (EZ.graph_mem s hs))).mdifferentiableAt (by simp)
  have hD := rawHorizontalCovariantDerivative_isCovariantDerivative G.leafwise
  have hadd := hD.add hY ((mdifferentiableAt_const (c := c)).smul_section hZ)
  have hsmul := hD.smul_const c hZ
  change rawHorizontalCovariantDerivative G.leafwise (EY.extension s + c • EZ.extension s)
      (γ s) = rawHorizontalCovariantDerivative G.leafwise (EY.extension s) (γ s) +
        rawHorizontalCovariantDerivative G.leafwise (c • EZ.extension s) (γ s) at hadd
  rw [hsmul] at hadd
  change deriv (fun r => EY.extension r (γ s) + c • EZ.extension r (γ s)) s +
    rawHorizontalCovariantDerivative G.leafwise (EY.extension s + c • EZ.extension s) (γ s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ)) = _
  rw [hd, hadd]
  simp only [M14HorizontalCovariantDerivative, add_apply, smul_apply, smul_add]
  abel




theorem horizontalCovariantDerivative_affine_congr
    (EY : M14PullbackExtension G γ J Y) (EZ : M14PullbackExtension G γ J Z)
    (EH : M14PullbackExtension G γ J H) (c : ℝ)
    (hH : ∀ s ∈ J, H s = Y s + c • Z s) {s : ℝ} (hs : s ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J s)
    (hγ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s) :
    M14HorizontalCovariantDerivative G γ J H EH s =
      M14HorizontalCovariantDerivative G γ J Y EY s +
        c • M14HorizontalCovariantDerivative G γ J Z EZ s := by
  let EA := pullbackExtensionCongrOn EH (fun _ _ => rfl) (fun r hr => heq_of_eq (hH r hr))
  have h := eq_of_heq
    (horizontalCovariantDerivative_congrOn EH (fun _ _ => rfl)
      (fun r hr => heq_of_eq (hH r hr)) hs)
  exact h.trans ((horizontalCovariantDerivative_extension_independent EA
    (affinePullbackExtension EY EZ c) hs hJ hγ).trans
      (horizontalCovariantDerivative_affine EY EZ c hs))

end PoincareConjecture.M14
