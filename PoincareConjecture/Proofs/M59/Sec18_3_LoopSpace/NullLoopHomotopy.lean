import PoincareConjecture.Proofs.M59.Mathlib.SphereExtension
import PoincareConjecture.Proofs.M58.Sec18_4_LoopTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



def m59LoopSphereMap (gamma : C1FreeLoopSpace (M := M)) :
    C(Metric.sphere (0 : LoopPlane) 1, M) :=
  ⟨fun z => gamma ⟨z.val, mem_sphere_zero_iff_norm.mp z.property⟩,
    gamma.continuous.comp (continuous_subtype_val.subtype_mk _)⟩



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



def m59LoopPathSphereHomotopy {gamma delta : C1FreeLoopSpace (M := M)} (p : Path gamma delta) :
    (m59LoopSphereMap gamma).Homotopy (m59LoopSphereMap delta) where
  toFun q := p q.1 ⟨q.2.val, mem_sphere_zero_iff_norm.mp q.2.property⟩
  continuous_toFun := Proofs.M58.continuous_loop_eval.comp
    ((p.continuous.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _))
  map_zero_left _ := congrArg (fun g : C1FreeLoopSpace (M := M) => g _) p.source
  map_one_left _ := congrArg (fun g : C1FreeLoopSpace (M := M) => g _) p.target



theorem m59NullLoop_of_path {gamma delta : C1FreeLoopSpace (M := M)}
    (p : Path gamma delta) (hdelta : IsNullHomotopicLoop delta) : IsNullHomotopicLoop gamma := by
  apply (m59NullLoop_iff_sphereMap_nullhomotopic gamma).mpr
  obtain ⟨y, hy⟩ := (m59NullLoop_iff_sphereMap_nullhomotopic delta).mp hdelta
  exact ⟨y, (show (m59LoopSphereMap gamma).Homotopic (m59LoopSphereMap delta) from
    ⟨m59LoopPathSphereHomotopy p⟩).trans hy⟩



theorem m59NullLoop_of_inIdentityComponent (x : M) (gamma : C1FreeLoopSpace (M := M))
    (h : InIdentityComponent x gamma) : IsNullHomotopicLoop gamma := by
  obtain ⟨H, hH, h0, h1⟩ := h
  exact m59NullLoop_of_path ⟨⟨H, hH⟩, h0, h1⟩ ⟨fun _ => x, continuous_const, fun _ => rfl⟩

end PoincareConjecture
