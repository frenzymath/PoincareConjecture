import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}




lemma contMDiffAt_connection_extend
    [T2Space M]
    (D : LeviCivitaData g) {x : M} (z : TangentSpace (𝓡 n) x) :
    ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      ∞ (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) y
        (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z) y)) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let Z := FiberBundle.extend E z
  obtain ⟨u, hu, hZu⟩ := FiberBundle.exists_contMDiffOn_extend
    (I := 𝓡 n) (F := E) (k := (∞ : WithTop ℕ∞)) z
  obtain ⟨v, hvu, hvopen, hxv⟩ := mem_nhds_iff.mp hu
  obtain ⟨f, -, hf⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (hvopen.mem_nhds hxv)
  let W := f.toFun • Z
  have hW := ContMDiffOn.smul_section_of_tsupport (u := v) (s := Z)
    (ψ := f.toFun) f.contMDiff.contMDiffOn hvopen hf (hZu.mono hvu)
  have hCW := D.smooth.contMDiff.contMDiff hW.contMDiffOn
  have hCW' := contMDiffOn_univ.mp hCW
  have hCWx := hCW' x
  have heqW : ∀ᶠ y in 𝓝 x, W y = Z y := by
    filter_upwards [f.eventuallyEq_one] with y hy
    simp [W, hy]
  have heq : ∀ᶠ y in 𝓝 x, D.connection W y = D.connection Z y := by
    have heqW' : ∀ᶠ y in 𝓝 x, W =ᶠ[𝓝 y] Z :=
      eventually_eventuallyEq_nhds.mpr heqW
    filter_upwards [heqW', hvopen.mem_nhds hxv] with y hyEq hyv
    apply D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((hW y).mdifferentiableAt (by simp))
      (((hZu.mono hvu y hyv).contMDiffAt (hvopen.mem_nhds hyv)).mdifferentiableAt (by simp))
      Filter.univ_mem hyEq
  apply hCWx.congr_of_eventuallyEq
  exact heq.mono
    (fun y hy => congrArg (fun A => Bundle.TotalSpace.mk' (E →L[ℝ] E) y A) hy.symm)

end PoincareConjecture.LeviCivitaData
