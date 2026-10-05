import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Differential.PullbackSectionSmooth
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Extension.ProductExtension
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Gluing horizontal extensions along a closed graph

Morgan-Tian Lemmas 6.4 and 6.8, pp. 107-109. Apply smooth convex-section
gluing to the horizontal bundle pulled back to parameter times spacetime.
The closed graph prescribes the field, and outside it there is no constraint.
The global smooth section supplies one common spatial extension domain.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}

-- The pulled-back horizontal fiber is the original fiber at the second projection.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- Convex-section gluing unfolds the product pullback and its dependent fiber instances.
/-- Local extensions along a closed parameterized graph glue to an actual
extension on a common spatial domain, Lemmas 6.4 and 6.8, pp. 107-109. -/
theorem exists_pullbackExtension_of_closed_local
    (hJ : IsClosed J) (hγ : ContinuousOn γ J)
    (hloc : ∀ s ∈ J, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧
      Nonempty (M14PullbackExtension G γ (J ∩ U) Y)) :
    Nonempty (M14PullbackExtension G γ J Y) := by
  classical
  let : LocallyCompactSpace (EuclideanHalfSpace 1) := by
    change LocallyCompactSpace {v : EuclideanSpace ℝ (Fin 1) // 0 ≤ v 0}
    have hc : Continuous (fun v : EuclideanSpace ℝ (Fin 1) => v 0) := by
      fun_prop
    exact (isClosed_le continuous_const hc).locallyCompactSpace
  let : LocallyCompactSpace
      (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) :=
    inferInstanceAs (LocallyCompactSpace
      (EuclideanHalfSpace 1 × EuclideanSpace ℝ (Fin n)))
  let : LocallyCompactSpace G.Point := ChartedSpace.locallyCompactSpace
    (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) G.Point
  let f : ContMDiffMap ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (spacetimeModel n) (ℝ × G.Point) G.Point ∞ :=
    ⟨Prod.snd, contMDiff_snd⟩
  let : ∀ z, AddCommGroup (((f : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) z) :=
    fun z => inferInstanceAs (AddCommGroup (G.Horizontal (f z)))
  let A : Set (ℝ × G.Point) := {z | z.1 ∈ J ∧ γ z.1 = z.2}
  have hA : IsClosed A :=
    (hJ.preimage continuous_fst).isClosed_eq
      (hγ.comp continuous_fst.continuousOn (fun _ hz => hz))
      continuous_snd.continuousOn
  let t (z : ℝ × G.Point) : Set (((f : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) z) :=
    {v | ∀ h : γ z.1 = z.2, z.1 ∈ J → v = (h ▸ Y z.1 : G.Horizontal z.2)}
  have ht (z : ℝ × G.Point) : Convex ℝ (t z) := by
    intro v hv w hw a b _ _ hab h hzJ
    rw [hv h hzJ, hw h hzJ, ← add_smul, hab, one_smul]
  have hlocal (z : ℝ × G.Point) : ∃ U ∈ 𝓝 z,
      ∃ v : ∀ w, ((f : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) w,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
          (((𝓘(ℝ, ℝ)).prod (spacetimeModel n)).prod
            𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          (fun w => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w (v w)) U ∧
        ∀ w ∈ U, v w ∈ t w := by
    by_cases hz : z ∈ A
    · rcases z with ⟨s, p⟩
      rcases hz with ⟨hsJ, hsp⟩
      change γ s = p at hsp
      subst p
      obtain ⟨U, hU, hsU, ⟨L⟩⟩ := hloc s hsJ
      obtain ⟨D, hD, hgraph, hsm⟩ := L.joint_smooth
      let N := (U ×ˢ Set.univ) ∩ D
      have hN : N ∈ 𝓝 (s, γ s) :=
        ((hU.prod isOpen_univ).inter hD).mem_nhds
          ⟨⟨hsU, Set.mem_univ _⟩, hgraph s ⟨hsJ, hsU⟩⟩
      refine ⟨N, hN, (fun w => L.extension w.1 w.2), ?_, ?_⟩
      · intro w hw
        exact (Bundle.contMDiffWithinAt_pullback_section_iff f
          (fun w => L.extension w.1 w.2) N w).mpr
          ((hsm w hw.2).mono Set.inter_subset_right)
      · intro w hw h hwJ
        rcases w with ⟨r, q⟩
        change γ r = q at h
        subst q
        exact L.agrees r ⟨hwJ, hw.1.1⟩
    · refine ⟨Aᶜ, hA.isOpen_compl.mem_nhds hz, (fun _ => 0),
        (Bundle.contMDiff_zeroSection ℝ _).contMDiffOn, ?_⟩
      intro w hw h hwJ
      exact (hw ⟨hwJ, h⟩).elim
  obtain ⟨V, hV⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
    (F_fiber := EuclideanSpace ℝ (Fin n))
    ((f : ℝ × G.Point → G.Point) *ᵖ G.Horizontal) t ht hlocal
  have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal) z.2 (V z)) := by
    intro z
    apply contMDiffWithinAt_univ.mp
    exact (Bundle.contMDiffWithinAt_pullback_section_iff f V Set.univ z).mp
      (V.contMDiff z).contMDiffWithinAt
  refine ⟨pullbackExtensionOfGlobalSmooth (fun s p => V (s, p)) hs ?_⟩
  intro s hsJ
  exact hV (s, γ s) rfl hsJ

end PoincareMT.M14
