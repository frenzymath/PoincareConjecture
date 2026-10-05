import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.SphereDescent
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.CubeSphereHomotopy

/-!
# Based homotopies of normalized sphere families

The literal basepoint and sphere-parameter equalities identify the carried
classes with based cubes in one type. Equality of these classes supplies
a sphere homotopy fixing the pole. Source: MT Claim 18.16 and Definition
18.17, printed p. 430.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The carried cube viewed at the exact normalized point. Source:
MT Definition 18.17, printed p. 430. -/
def m59NormalizedCube (q : M59SphereQuotient) (x : M)
    (Gamma : FreeTwoSphereFamily (M := M)) (hGamma : M59NormalizedAt q x Gamma) :
    GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x) :=
  ⟨Gamma.class_certificate.cube_representative, fun z hz =>
    (Gamma.class_certificate.boundary_const z hz).trans (congrArg constantC1Loop hGamma.1)⟩

/-- The normalized cube represents the displayed family with exactly q.map.
Source: MT Definition 18.17, printed p. 430. -/
theorem m59NormalizedCube_agreement (q : M59SphereQuotient) (x : M)
    (Gamma : FreeTwoSphereFamily (M := M)) (hGamma : M59NormalizedAt q x Gamma)
    (z : Fin 2 → I) : m59NormalizedCube q x Gamma hGamma z = m59FamilyMap Gamma (q.map z) := by
  change Gamma.class_certificate.cube_representative z = Gamma.family (q.map z)
  rw [← hGamma.2]
  exact Gamma.class_certificate.family_agreement z

/-- The normalized cube's dependent class is the original certificate class.
Source: MT Definition 18.17, printed p. 430. -/
theorem m59NormalizedCube_sigma (q : M59SphereQuotient) (x : M)
    (Gamma : FreeTwoSphereFamily (M := M)) (hGamma : M59NormalizedAt q x Gamma) :
    (⟨x, Quotient.mk' (m59NormalizedCube q x Gamma hGamma)⟩ :
      Σ y : M, HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop y)) =
        familySigmaClass Gamma := by
  obtain ⟨hbase, _⟩ := hGamma
  subst x
  exact congrArg (Sigma.mk Gamma.basepoint) Gamma.class_certificate.class_eq.symm

/-- Equality of normalized classes gives an actual sphere homotopy fixing
the constant-loop pole. Source: MT Claim 18.16, printed p. 430. -/
theorem m59SphereHomotopy_of_class_eq (q : M59SphereQuotient) (x : M)
    (Gamma Delta : FreeTwoSphereFamily (M := M))
    (hGamma : M59NormalizedAt q x Gamma) (hDelta : M59NormalizedAt q x Delta)
    (hclass : familySigmaClass Gamma = familySigmaClass Delta) :
    ∃ H : (m59FamilyMap Gamma).Homotopy (m59FamilyMap Delta),
      ∀ t : I, H (t, q.pole) = constantC1Loop x := by
  let a := m59NormalizedCube q x Gamma hGamma
  let b := m59NormalizedCube q x Delta hDelta
  have heq : (⟨x, Quotient.mk' a⟩ :
      Σ y : M, HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop y)) =
        ⟨x, Quotient.mk' b⟩ :=
    (m59NormalizedCube_sigma q x Gamma hGamma).trans
      (hclass.trans (m59NormalizedCube_sigma q x Delta hDelta).symm)
  have hab : (Quotient.mk' a : HomotopyGroup.Pi 2 _ (constantC1Loop x)) = Quotient.mk' b :=
    eq_of_heq (Sigma.mk.inj heq).2
  obtain ⟨K⟩ : GenLoop.Homotopic a b := Quotient.exact hab
  let T := GenLoop.HomotopyAlong.ofRel K
  let H := T.sphereHomotopy q.map q.surjective q.exact_fibers
    (m59FamilyMap Gamma) (m59FamilyMap Delta)
    (m59NormalizedCube_agreement q x Gamma hGamma) (m59NormalizedCube_agreement q x Delta hDelta)
  refine ⟨H, ?_⟩
  intro t
  have hzero : (fun _ : Fin 2 => (0 : I)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  calc
    H (t, q.pole) = H (t, q.map (fun _ => 0)) :=
      congrArg (fun c => H (t, c)) (q.boundary_collapsed _ hzero).symm
    _ = T.toHomotopy (t, fun _ => 0) := T.sphereHomotopy_apply q.map q.surjective q.exact_fibers
      (m59FamilyMap Gamma) (m59FamilyMap Delta)
      (m59NormalizedCube_agreement q x Gamma hGamma)
      (m59NormalizedCube_agreement q x Delta hDelta) t _
    _ = constantC1Loop x := T.boundary_path t ⟨_, hzero⟩

end PoincareMT
