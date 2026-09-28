import PoincareConjecture.Proofs.M58.Sec18_4_LoopTopology
import PoincareConjecture.Proofs.M02.HomotopyMap

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology unitInterval

universe u

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem constant_loops_homotopic_const (x : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M x))
    (p : GenLoop (Fin 2) M x) :
    GenLoop.Homotopic (M02.mapGenLoop constantLoopMap rfl p)
      (GenLoop.const : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x)) := by
  have hp : GenLoop.Homotopic p (GenLoop.const : GenLoop (Fin 2) M x) :=
    Quotient.exact (hpi.elim (⟦p⟧ : HomotopyGroup.Pi 2 M x) ⟦GenLoop.const⟧)
  exact M02.mapGenLoop_homotopic constantLoopMap rfl hp

theorem loop_class_eq_one_of_based_contraction (x : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M x)) (z : LoopCircle)
    (r : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (H : r.val.HomotopicRel
      (constantLoopMap.comp ((loopEvaluation z).comp r.val)) (Cube.boundary (Fin 2))) :
    Quotient.mk' r =
      (1 : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) := by
  let p : GenLoop (Fin 2) M x := M02.mapGenLoop (loopEvaluation z) rfl r
  apply Quotient.sound
  exact H.trans (constant_loops_homotopic_const x hpi p)

theorem family_class_eq_one_of_contraction
    (source : FreeTwoSphereFamily (M := M))
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M source.basepoint)) (z : LoopCircle)
    (H : C(I × LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (h0 : ∀ c, H (0, c) = source.family c)
    (h1 : ∀ c, H (1, c) = constantC1Loop (source.family c z))
    (hfixed : ∀ t c, source.family c = constantC1Loop source.basepoint →
      H (t, c) = constantC1Loop source.basepoint) :
    source.homotopy_class = 1 := by
  let cert := source.class_certificate
  let r : GenLoop (Fin 2) (C1FreeLoopSpace (M := M))
      (constantC1Loop source.basepoint) :=
    ⟨cert.cube_representative, cert.boundary_const⟩
  rw [cert.class_eq]
  apply loop_class_eq_one_of_based_contraction source.basepoint hpi z r
  refine ⟨{
    toFun := fun p => H (p.1, cert.sphere_parameter p.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (cert.sphere_parameter.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro y
    exact (h0 _).trans (cert.family_agreement y).symm
  · intro y
    change H (1, cert.sphere_parameter y) = constantC1Loop (cert.cube_representative y z)
    rw [h1, cert.family_agreement]
  · intro t y hy
    change H (t, cert.sphere_parameter y) = cert.cube_representative y
    rw [cert.boundary_const y hy]
    apply hfixed
    exact (cert.family_agreement y).symm.trans (cert.boundary_const y hy)

end PoincareConjecture.Proofs.M58
