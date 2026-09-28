import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Collars.OriginalAnnularMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.RadialIsotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.ZeroWindingEndpoint
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Original.AnnularStraightening
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.ContactInduction

set_option autoImplicit false
open Set Geometry PLAnnularStrip unitInterval

namespace PoincareConjecture.M76.CollarIsotopy

open PoincareConjecture.M76.Dehn
local notation "Ann" => squareAnnulus 8 1
local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => Metric.sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem annularTwistPostcomposition_core_parameter
    {Q : Type*} [TopologicalSpace Q] (D : Ann ≃ₜ Ann) (n : ℤ)
    (gamma : Q → Ann) (q : Q ≃ₜ Circle)
    (hq : ∀ x, D (gamma x) = annulusCoreCircle (q x)) :
    ∃ q' : Q ≃ₜ Circle, ∀ x,
      (D.trans (annularIntegerTwist n)) (gamma x) = annulusCoreCircle (q' x) := by
  refine ⟨q.trans (Homeomorph.addRight ((16 * (n : ℝ) : ℝ) : Circle)), ?_⟩
  intro x
  change annularIntegerTwist n (D (gamma x)) = _
  rw [hq, annularIntegerTwist_core]
  rfl

theorem exists_original_annular_endpoint_collar_motion
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U B : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hne : (interior R).Nonempty)
    (hU : IsOpen U) (hBU : frontier R ⊆ U)
    (A : Ann ≃ₜ B) (hBS : B ⊆ frontier R) (hB : IsClosed B)
    (j : (ℝ × ℝ) → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ z : Ann, j z = (A z : X))
    (hopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A))
    (D : Ann ≃ₜ Ann) (hD : HasJointPLAnnularIsotopy D) :
    ∃ G : I → R ≃ₜ R,
      Continuous (fun z : I × R => G z.1 z.2) ∧
      Continuous (fun z : I × R => (G z.1).symm z.2) ∧ G 0 = Homeomorph.refl R ∧
      (∀ t : I, ChartwisePLHomeomorph e e (G t)) ∧
      (∀ (t : I) (x : R), (G t x : X) ∈ frontier R ↔ (x : X) ∈ frontier R) ∧
      (∀ z : Ann,
        (G 1 ⟨A z, he.closed.frontier_subset (hBS (A z).property)⟩ : X) = A (D z)) ∧
      (∀ t : I, ∀ x : R, (x : X) ∉ U → G t x = x) ∧
      (∀ t : I, ∀ x : R, (x : X) ∈ frontier R →
        (x : X) ∉ originalAnnulusOpenMark A → G t x = x) := by
  obtain ⟨H, F, _, h0, h1, hF, _, hv, _, hc, hci, hrims⟩ := hD
  have hfix (t : I) (x : Ann)
      (hx : depth 8 (x : ℝ × ℝ) = -1 ∨ depth 8 (x : ℝ × ℝ) = 1) : H t x = x := by
    rcases hx with hx | hx
    · obtain ⟨z, rfl⟩ := (range_annulusRimPoint false).symm.subset hx
      exact hrims t false z
    · obtain ⟨z, rfl⟩ := (range_annulusRimPoint true).symm.subset hx
      exact hrims t true z
  obtain ⟨G, hGc, hGci, hG0, hGPL, hGA, hout, hmark⟩ :=
    exists_original_annular_collar_motion he hR hne hU hBU A hBS hB j hj hjval hopen
      H hc hci (fun x => by rw [h0]; rfl) hfix F hF hv
  have hforward (t : I) (x : R) (hx : (x : X) ∈ frontier R) :
      (G t x : X) ∈ frontier R := by
    by_cases hb : (x : X) ∈ B
    · let z := A.symm ⟨x, hb⟩
      have hz : (⟨A z, he.closed.frontier_subset (hBS (A z).property)⟩ : R) = x :=
        Subtype.ext (congrArg (fun y : B => (y : X)) (A.apply_symm_apply ⟨x, hb⟩))
      rw [← hz, hGA]
      exact hBS (A (H t z)).property
    · rw [hmark t x hx (fun hm => hb (originalAnnulusOpenMark_subset A hm))]
      exact hx
  have honto (t : I) (x : R) (hx : (x : X) ∈ frontier R) :
      ∃ y : R, (y : X) ∈ frontier R ∧ G t y = x := by
    by_cases hb : (x : X) ∈ B
    · let z := (H t).symm (A.symm ⟨x, hb⟩)
      refine ⟨⟨A z, he.closed.frontier_subset (hBS (A z).property)⟩,
        hBS (A z).property, Subtype.ext ?_⟩
      rw [hGA]
      change (A (H t ((H t).symm (A.symm ⟨x, hb⟩))) : X) = x
      rw [(H t).apply_symm_apply, A.apply_symm_apply]
    · exact ⟨x, hx, hmark t x hx (fun hm => hb (originalAnnulusOpenMark_subset A hm))⟩
  refine ⟨G, hGc, hGci, hG0, hGPL, ?_, ?_, hout, hmark⟩
  · intro t x
    refine ⟨fun hx => ?_, hforward t x⟩
    obtain ⟨y, hy, heq⟩ := honto t (G t x) hx
    exact (G t).injective heq ▸ hy
  · intro z
    rw [hGA, h1]

theorem exists_original_annular_circle_collar_motion_of_endpoint
    {X Q ι : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Q]
    {e : ι → OpenPartialHomeomorph X V3} {R U B : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hne : (interior R).Nonempty)
    (hU : IsOpen U) (hBU : frontier R ⊆ U)
    (A : Ann ≃ₜ B) (hBS : B ⊆ frontier R) (hB : IsClosed B)
    (j : (ℝ × ℝ) → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ z : Ann, j z = (A z : X))
    (hopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A))
    (D : Ann ≃ₜ Ann) (hD : HasJointPLAnnularIsotopy D)
    (gamma : Q → B) (q : Q ≃ₜ Circle)
    (hq : ∀ x, D (A.symm (gamma x)) = annulusCoreCircle (q x)) :
    ∃ G : I → R ≃ₜ R,
      Continuous (fun z : I × R => G z.1 z.2) ∧
      Continuous (fun z : I × R => (G z.1).symm z.2) ∧ G 0 = Homeomorph.refl R ∧
      (∀ t : I, ChartwisePLHomeomorph e e (G t)) ∧
      (∀ (t : I) (x : R), (G t x : X) ∈ frontier R ↔ (x : X) ∈ frontier R) ∧
      (∀ x : Q, (G 1 ⟨gamma x,
        he.closed.frontier_subset (hBS (gamma x).property)⟩ : X) =
          A (annulusCoreCircle (q x))) ∧
      G 1 '' range (fun x : Q => (⟨gamma x,
        he.closed.frontier_subset (hBS (gamma x).property)⟩ : R)) =
        range (fun z : Circle => (⟨A (annulusCoreCircle z),
          he.closed.frontier_subset (hBS (A (annulusCoreCircle z)).property)⟩ : R)) ∧
      (∀ t : I, ∀ x : R, (x : X) ∉ U → G t x = x) ∧
      (∀ t : I, ∀ x : R, (x : X) ∈ frontier R →
        (x : X) ∉ originalAnnulusOpenMark A → G t x = x) := by
  obtain ⟨G, hGc, hGci, hG0, hGPL, hfront, hGA, hout, hmark⟩ :=
    exists_original_annular_endpoint_collar_motion he hR hne hU hBU A hBS hB j hj hjval
      hopen D hD
  have hpoint (x : Q) : (G 1 ⟨gamma x,
      he.closed.frontier_subset (hBS (gamma x).property)⟩ : X) =
        A (annulusCoreCircle (q x)) := by
    simpa only [A.apply_symm_apply, hq x] using hGA (A.symm (gamma x))
  refine ⟨G, hGc, hGci, hG0, hGPL, hfront, hpoint, ?_, hout, hmark⟩
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨q x, (Subtype.ext (hpoint x)).symm⟩
  · rintro _ ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := q.surjective z
    exact ⟨_, mem_range_self x, Subtype.ext (hpoint x)⟩

theorem exists_original_annular_circle_collar_straightening
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R U B : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hne : (interior R).Nonempty)
    (hU : IsOpen U) (hBU : frontier R ⊆ U)
    (A : Ann ≃ₜ B) (hBS : B ⊆ frontier R) (hB : IsClosed B)
    (j : (ℝ × ℝ) → X) (hj : PolyhedralPLInCharts e j Ann)
    (hjval : ∀ z : Ann, j z = (A z : X))
    (hopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' originalAnnulusOpenMark A))
    (gamma : C(Q2, B)) (hinj : Function.Injective gamma)
    (g : V2 → X) (hg : PolyhedralPLInCharts e g Q2)
    (hgval : ∀ x : Q2, g x = (gamma x : X))
    (hdepth : ∀ x : Q2, -1 < depth 8 (A.symm (gamma x) : ℝ × ℝ) ∧
      depth 8 (A.symm (gamma x) : ℝ × ℝ) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map
        (((ContinuousMap.inclusion (hBS.trans he.closed.frontier_subset)).comp gamma).continuous)))
          ≠ 1) :
    ∃ (G : I → R ≃ₜ R) (q : Q2 ≃ₜ Circle),
      Continuous (fun z : I × R => G z.1 z.2) ∧
      Continuous (fun z : I × R => (G z.1).symm z.2) ∧ G 0 = Homeomorph.refl R ∧
      (∀ t : I, ChartwisePLHomeomorph e e (G t)) ∧
      (∀ (t : I) (x : R), (G t x : X) ∈ frontier R ↔ (x : X) ∈ frontier R) ∧
      (∀ x : Q2, (G 1 ⟨gamma x,
        he.closed.frontier_subset (hBS (gamma x).property)⟩ : X) =
          A (annulusCoreCircle (q x))) ∧
      G 1 '' range (fun x : Q2 => (⟨gamma x,
        he.closed.frontier_subset (hBS (gamma x).property)⟩ : R)) =
        range (fun z : Circle => (⟨A (annulusCoreCircle z),
          he.closed.frontier_subset (hBS (A (annulusCoreCircle z)).property)⟩ : R)) ∧
      (∀ t : I, ∀ x : R, (x : X) ∉ U → G t x = x) ∧
      (∀ t : I, ∀ x : R, (x : X) ∈ frontier R →
        (x : X) ∉ originalAnnulusOpenMark A → G t x = x) := by
  have hessentialB : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1 := by
    intro hn
    have h := congrArg
      (FundamentalGroup.map (ContinuousMap.inclusion (hBS.trans he.closed.frontier_subset))
        (gamma squareRimBase)) hn
    rw [map_one] at h
    exact hessential h
  obtain ⟨D, hD, _, hfix, _, q, hq⟩ := exists_originalPL_annular_straightening
    e he.compatible A j hj hjval gamma hinj g hg hgval hdepth hessentialB
  obtain ⟨n, hD', _, hfix', _, _, f, r, _, _, hinj', _, _, _,
      hr, _, hr0, hr1, _, hheight, hproper, hproj, _⟩ :=
    exists_zero_winding_annular_endpoint D hD hfix
  let D' := D.trans (annularIntegerTwist (-n))
  have hstraight : HasJointPLRadialStraightening (annularRadialImage D') :=
    hasJointPLRadialStraightening_of_zero_winding_lift
      (annularRadialImage D') hinj' r hr hr0 hr1 hproj
      (fun t => hheight t t.property) hproper
  have hmotion : HasJointPLAnnularIsotopy D' :=
    hasJointPLAnnularIsotopy_of_radial_straightening D' hD'
      (fun side z => hfix' _ (by rw [depth_annulusRimPoint]; cases side <;> simp)) hstraight
  obtain ⟨q', hq'⟩ := annularTwistPostcomposition_core_parameter D (-n)
    (fun x => A.symm (gamma x)) q hq
  obtain ⟨G, hG⟩ := exists_original_annular_circle_collar_motion_of_endpoint
    he hR hne hU hBU A hBS hB j hj hjval hopen D' hmotion gamma q' hq'
  exact ⟨G, q', hG⟩

end PoincareConjecture.M76.CollarIsotopy
