import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.SphereExtension
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops

/-!
# Continuous fillings and paths of C1 loops

A path of C1 loops gives a homotopy of circle values. Cone extension turns
a path to a constant loop into the whole-plane filling in the frozen
definition. This is one direction of MT Claim 18.16, printed p. 430; the
converse C1 approximation argument is separate.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- Circle values in the standard metric-sphere model. Source: the circle
convention of MT, pp. 429-430. -/
def m59LoopSphereMap (gamma : C1FreeLoopSpace (M := M)) :
    C(Metric.sphere (0 : LoopPlane) 1, M) :=
  ⟨fun z => gamma ⟨z.val, mem_sphere_zero_iff_norm.mp z.property⟩,
    gamma.continuous.comp (continuous_subtype_val.subtype_mk _)⟩

/-- The filling convention is equivalent to a nullhomotopy of circle values.
Source: MT Claim 18.16, p. 430; Hatcher Lemma 4.7, p. 348. -/
theorem m59NullLoop_iff_sphereMap_nullhomotopic (gamma : C1FreeLoopSpace (M := M)) :
    IsNullHomotopicLoop gamma ↔ (m59LoopSphereMap gamma).Nullhomotopic := by
  constructor
  · rintro ⟨F, hF, hboundary⟩
    refine ⟨F 0, ⟨{
      toFun := fun p => F ((1 - (p.1 : ℝ)) • p.2.val)
      continuous_toFun := hF.comp
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp continuous_snd))
      map_zero_left := ?_
      map_one_left := ?_ }⟩⟩
    · intro z
      simpa [m59LoopSphereMap] using hboundary ⟨z.val, mem_sphere_zero_iff_norm.mp z.property⟩
    · intro z
      simp
  · intro h
    obtain ⟨F, hF⟩ := Proofs.M59.exists_extension_of_sphere_nullhomotopic (m59LoopSphereMap gamma) h
    refine ⟨F, F.continuous, ?_⟩
    intro z
    exact hF ⟨z.val, mem_sphere_zero_iff_norm.mpr z.property⟩

/-- A C1-loop path supplies a homotopy of the underlying sphere maps.
Source: MT Claim 18.16, printed p. 430. -/
def m59LoopPathSphereHomotopy {gamma delta : C1FreeLoopSpace (M := M)} (p : Path gamma delta) :
    (m59LoopSphereMap gamma).Homotopy (m59LoopSphereMap delta) where
  toFun q := p q.1 ⟨q.2.val, mem_sphere_zero_iff_norm.mp q.2.property⟩
  continuous_toFun := Proofs.M58.continuous_loop_eval.comp
    ((p.continuous.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _))
  map_zero_left _ := congrArg (fun g : C1FreeLoopSpace (M := M) => g _) p.source
  map_one_left _ := congrArg (fun g : C1FreeLoopSpace (M := M) => g _) p.target

/-- A path to a null loop preserves the existence of a continuous filling.
Source: MT Claim 18.16, printed p. 430. -/
theorem m59NullLoop_of_path {gamma delta : C1FreeLoopSpace (M := M)}
    (p : Path gamma delta) (hdelta : IsNullHomotopicLoop delta) : IsNullHomotopicLoop gamma := by
  apply (m59NullLoop_iff_sphereMap_nullhomotopic gamma).mpr
  obtain ⟨y, hy⟩ := (m59NullLoop_iff_sphereMap_nullhomotopic delta).mp hdelta
  exact ⟨y, (show (m59LoopSphereMap gamma).Homotopic (m59LoopSphereMap delta) from
    ⟨m59LoopPathSphereHomotopy p⟩).trans hy⟩

/-- A path from a C1 loop to the chosen constant loop gives a filling.
Source: the forward identity-component implication in MT Claim 18.16, p. 430. -/
theorem m59NullLoop_of_inIdentityComponent (x : M) (gamma : C1FreeLoopSpace (M := M))
    (h : InIdentityComponent x gamma) : IsNullHomotopicLoop gamma := by
  obtain ⟨H, hH, h0, h1⟩ := h
  exact m59NullLoop_of_path ⟨⟨H, hH⟩, h0, h1⟩ ⟨fun _ => x, continuous_const, fun _ => rfl⟩

end PoincareMT
