import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CylinderCurvature
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_CanonicalScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_PinchingBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_cylinder_scalar_doubling_constant
    (P : M44CapPersistencePredecessors.{u}) (K : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (F : SurgeryFlowData.{u}) (C : GeneralizedSliceCarrier.{u})
      {origin scale B T : ℝ} {U : Set C.carrier}
      (e : SurgeryFlowCylinder F C origin scale (Ico 0 B) U),
      IsOpen U → ∀ f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞,
      f.target ⊆ U → ∀ G : CylinderRicciFlow e f, 0 < T → T < B →
      ∀ {q M : ℝ}, 0 < M → q ≤ M →
      (∀ s ∈ Ico (0 : ℝ) T, ∀ x : (⟨f.target, f.open_target⟩ : Opens C.carrier),
        q ≤ (G.flow.connection s).scalarCurvature x →
        ∀ hs : s ∈ Ico 0 B,
          SurgeryCanonicalControl F (origin + s / scale) (cylinderTargetTransport e f s hs x)
            F.parameters.epsilon K ∧
          ¬ ∃ N : SingularCComponent (F.metric (origin + s / scale))
            (F.connection (origin + s / scale)) K, cylinderTargetTransport e f s hs x ∈ N.carrier) →
      (∀ x, (G.flow.connection 0).scalarCurvature x ≤ M) →
      8 * L * M * T ≤ 1 →
      ∀ s ∈ Icc (0 : ℝ) T, ∀ x, (G.flow.connection s).scalarCurvature x ≤ 2 * M := by
  obtain ⟨L, hL, hbound⟩ := exists_surgery_canonical_scalar_evolution_bound P K
  refine ⟨L, hL, ?_⟩
  intro F C origin scale B T U e hU f hmap G hT hTB q M hM hq hcanonical hinitial hshort
    s hs x
  let phi (t : ℝ) := (G.flow.connection t).scalarCurvature x
  let d (t : ℝ) := (G.flow.connection t).laplacian (G.flow.connection t).scalarCurvature x +
    2 * (G.flow.connection t).ricciNormSq x
  have hsub : Icc (0 : ℝ) T ⊆ Ico 0 B := fun _ ht => ⟨ht.1, ht.2.trans_lt hTB⟩
  have hcont : ContinuousOn phi (Icc 0 T) := by
    intro t ht
    exact ((P.curvature.scalar_evolution 3
      (⟨f.target, f.open_target⟩ : Opens C.carrier) (Ico 0 B) G.flow t (hsub ht) x).mono
        hsub).continuousWithinAt
  have hderiv (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
      HasDerivWithinAt phi (d t) (Ici t) t := by
    apply (P.curvature.scalar_evolution 3
      (⟨f.target, f.open_target⟩ : Opens C.carrier) (Ico 0 B) G.flow t
        ⟨ht.1, ht.2.trans hTB⟩ x).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2)
      (fun y hy => ⟨ht.1.trans hy.1, hy.2.trans_lt hTB⟩)
  have hrate (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) (hhigh : q ≤ phi t) :
      d t ≤ L * phi t ^ 2 := by
    have htI : t ∈ Ico 0 B := ⟨ht.1, ht.2.trans hTB⟩
    obtain ⟨hc, hn⟩ := hcanonical t ht x hhigh htI
    have hphysical := hbound F (origin + t / scale) (cylinderTargetTransport e f t htI x) hc hn
    exact (le_abs_self (d t)).trans (G.scalar_evolution_bound P hU hmap t htI x hphysical)
  have htime : 8 * L * M * (T - 0) ≤ 1 := by simpa only [sub_zero] using hshort
  exact le_two_mul_of_deriv_le_sq_above hL hM hq hcont hderiv
    (hinitial x) hrate htime s hs

theorem exists_cylinder_curvature_bound
    (P : M44CapPersistencePredecessors.{u}) (K : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (F : SurgeryFlowData.{u}) (C : GeneralizedSliceCarrier.{u})
      {origin scale B T : ℝ} {U : Set C.carrier}
      (e : SurgeryFlowCylinder F C origin scale (Ico 0 B) U),
      IsOpen U → scale⁻¹ ≤ 1 →
      ∀ f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞,
      f.target ⊆ U → IsPreconnected f.target →
      ∀ G : CylinderRicciFlow e f, 0 < T → T < B →
      ∀ {q M : ℝ}, 0 < M → q ≤ M →
      (∀ s ∈ Ico (0 : ℝ) T, ∀ x : (⟨f.target, f.open_target⟩ : Opens C.carrier),
        q ≤ (G.flow.connection s).scalarCurvature x →
        ∀ hs : s ∈ Ico 0 B,
          SurgeryCanonicalControl F (origin + s / scale) (cylinderTargetTransport e f s hs x)
            F.parameters.epsilon K) →
      (∀ x, (G.flow.connection 0).scalarCurvature x ≤ M) →
      (∀ s ∈ Ico (0 : ℝ) T,
        ∃ x : (⟨f.target, f.open_target⟩ : Opens C.carrier),
        ∃ u v : TangentSpace (𝓡 3) x,
          LeviCivitaData.IsOrthonormalPair (G.flow.metric s) x u v ∧
          (G.flow.connection s).sectionalCurvature x u v <
            K⁻¹ * (G.flow.connection s).scalarCurvature x) →
      8 * L * M * T ≤ 1 → SurgeryFlowPinched F →
      ∀ s ∈ Icc (0 : ℝ) T, ∀ x,
        (G.flow.connection s).scalarCurvature x ≤ 2 * M ∧
        (G.flow.connection s).curvatureTensorNorm x ≤ 13 * max (2 * M) (Real.exp 4) := by
  obtain ⟨L, hL, hbound⟩ := exists_cylinder_scalar_doubling_constant P K
  refine ⟨L, hL, ?_⟩
  intro F C origin scale B T U e hU hsmall f hmap hconnected G hT hTB q M hM hq
    hcanonical hinitial hcollar hshort hpinch
  have hscalar := hbound F C e hU f hmap G hT hTB hM hq
    (fun s hs x hhigh hsI => by
      obtain ⟨p, u, v, horth, hmargin⟩ := hcollar s hs
      exact ⟨hcanonical s hs x hhigh hsI,
        G.not_component_of_collar P hU hmap hconnected s hsI p K u v horth hmargin x⟩)
    hinitial hshort
  intro s hs x
  have hsI : s ∈ Ico 0 B := ⟨hs.1, hs.2.trans_lt hTB⟩
  have htime : origin + s / scale ∈ F.time_domain :=
    e.time_subset (mem_image_of_mem _ hsI)
  have hR : scale⁻¹ * (F.connection (origin + s / scale)).scalarCurvature
      (cylinderTargetTransport e f s hsI x) ≤ 2 * M := by
    simpa only [G.scalar_eq hU hmap s hsI x, div_eq_mul_inv, mul_comm] using hscalar s hs x
  have hRm := (hpinch (origin + s / scale) htime).scaled_curvature_norm_le P
    (mem_univ (cylinderTargetTransport e f s hsI x)) (inv_pos.mpr e.scale_pos).le hsmall hR
  refine ⟨hscalar s hs x, ?_⟩
  simpa only [G.curvatureTensorNorm_eq hU hmap s hsI x, div_eq_mul_inv, mul_comm] using hRm

end PoincareConjecture.M44
