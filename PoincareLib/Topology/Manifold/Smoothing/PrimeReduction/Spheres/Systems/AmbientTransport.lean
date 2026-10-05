import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Isotopy.OriginalPLMotionComposition
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.SphereAmbientTransport

/-!
# Protected ambient transport of a sphere system

Composition uses the original atlas at each intermediate point. Global
coverage is supplied by the original PL domain. The transported members
retain their complete sphere parametrizations and remain pairwise disjoint.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- Both original-atlas PL directions compose, with reversed order for the
inverse. The intermediate chart is constructed using original coverage. -/
theorem original_PL_motion_trans_both
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (F G : X ≃ₜ X)
    (hF : ∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hFinv : ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hG : ∀ i j, (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hGinv : ∀ i j, (e i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) :
    (∀ i j, (e i).symm.trans ((F.trans G).toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) ∧
    (∀ i j, (e i).symm.trans ((F.trans G).symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) := by
  exact ⟨original_PL_motion_trans e hcover F G hF hG,
    original_PL_motion_trans e hcover G.symm F.symm hGinv hFinv⟩

/-- The actual composite and its inverse fix an open neighborhood of the
protected set. No invariant-neighborhood hypothesis is required. -/
theorem protected_ambient_trans_neighborhood
    {X : Type*} [TopologicalSpace X]
    (F G : X ≃ₜ X) {Z W V : Set X}
    (hW : IsOpen W) (hV : IsOpen V) (hZW : Z ⊆ W) (hZV : Z ⊆ V)
    (hF : EqOn F id W) (hG : EqOn G id V) :
    IsOpen (W ∩ V) ∧ Z ⊆ W ∩ V ∧
      EqOn (F.trans G) id (W ∩ V) ∧
      EqOn (F.trans G).symm id (W ∩ V) := by
  have hfix : EqOn (F.trans G) id (W ∩ V) := by
    intro x hx
    change G (F x) = x
    simpa only [hF hx.1, id_eq] using hG hx.2
  refine ⟨hW.inter hV, fun x hx => ⟨hZW hx, hZV hx⟩, hfix, ?_⟩
  intro x hx
  apply (F.trans G).injective
  simpa only [Homeomorph.apply_symm_apply, id_eq] using (hfix hx).symm

/-- Transport each complete sphere by the same actual original-atlas PL map.
The whole union remains disjoint from every set fixed by that map. -/
theorem protected_sphere_system_ambient_image
    {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (G : X ≃ₜ X)
    (hG : ∀ i j, (e i).symm.trans (G.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    {Z : Set X} (hSZ : Disjoint (⋃ i, S i) Z) (hfix : EqOn G id Z) :
    (∀ i, Nonempty (ChartwisePLSphere e (G '' S i))) ∧
    Pairwise (fun i j => Disjoint (G '' S i) (G '' S j)) ∧
    Disjoint (⋃ i, G '' S i) Z ∧
    G '' (⋃ i, S i) = ⋃ i, G '' S i := by
  refine ⟨fun i => (sS i).nonempty_image G hcover hG, ?_, ?_, image_iUnion⟩
  · intro i j hij
    exact (hdis hij).image G.injective.injOn (subset_univ _) (subset_univ _)
  · apply disjoint_left.mpr
    intro x hx hxZ
    obtain ⟨i, y, hy, hyx⟩ := mem_iUnion.mp hx
    have hyx' : y = x := G.injective (hyx.trans (hfix hxZ).symm)
    exact disjoint_left.mp hSZ (mem_iUnion.mpr ⟨i, hyx' ▸ hy⟩) hxZ

end PoincareMT.M76
