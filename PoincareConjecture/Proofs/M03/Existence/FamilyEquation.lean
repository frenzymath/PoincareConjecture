import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.Ch01.CurvatureConnection

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem hasDerivWithinAt_Ico_of_Ici
    {f : ℝ → ℝ} {d : ℝ} {T t : ℝ}
    (hT : 0 < T) (ht : t ∈ Set.Ico 0 T)
    (h : HasDerivWithinAt f d (Set.Ici 0) t) :
    HasDerivWithinAt f d (Set.Ico 0 T) t := by
  exact h.mono (fun s hs => hs.1)

theorem ricciEquation_connectionIndependent
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (t : ℝ) (ht : t ∈ J) (D D' : LeviCivitaData (g t))
    {x : M} {u v : TangentSpace (𝓡 n) x}
    (h : HasDerivWithinAt (fun s ↦ (g s).inner x u v)
      (-2 * D.ricci x u v) J t) :
    HasDerivWithinAt (fun s ↦ (g s).inner x u v)
      (-2 * D'.ricci x u v) J t := by
  rw [D.ricci_eq D' x u v] at h
  exact h

theorem metricFamily_of_selected_connection
    {g0 : RiemannianMetric n M} {T : ℝ}
    (hT : 0 < T) (g : ℝ → RiemannianMetric n M)
    (D : ∀ s : ℝ, LeviCivitaData (g s))
    (hg0 : g 0 = g0)
    (hsm : RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T))
    (hEq : ∀ (t : ℝ), t ∈ Set.Ici 0 → t < T → ∀ (x : M)
      (u v : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s ↦ (g s).inner x u v)
        (-2 * (D t).ricci x u v) (Set.Ici 0) t) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric n M,
      g 0 = g0 ∧ RiemannianMetric.IsSmoothFamilyOn g (Set.Ico 0 T) ∧
      ∀ (t : ℝ), t ∈ Set.Ico 0 T → ∀ (D' : LeviCivitaData (g t))
        (x : M) (u v : TangentSpace (𝓡 n) x),
        HasDerivWithinAt (fun s ↦ (g s).inner x u v)
          (-2 * D'.ricci x u v) (Set.Ico 0 T) t := by
  refine ⟨T, hT, g, hg0, hsm, ?_⟩
  intro t ht D' x u v
  have hIci := hEq t ht.1 ht.2 x u v
  have hIco := hasDerivWithinAt_Ico_of_Ici hT ht hIci
  exact ricciEquation_connectionIndependent t ht (D t) D' hIco

end PoincareConjecture
