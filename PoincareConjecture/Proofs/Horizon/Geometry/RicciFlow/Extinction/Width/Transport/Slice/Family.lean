import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Slice.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.ClassPath.Data

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow} {T : ℝ}
  {P : RepairedComponentPath D.flow T W}

noncomputable def m67SliceFamily
    (S : M59IdentificationSystem.{u})
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0))
    (datum : ∀ s, M67ClassDatum S (P.component s))
    (s : Set.Icc (0 : ℝ) T) : M67WidthSlice S.quotient (P.component s) := by
  classical
  exact if hs : s = m67InitialTime P then
    hs.symm ▸ m67InitialWidthSlice S (P.component (m67InitialTime P))
      (D.flow.metric 0) initial
  else m67ActualWidthSlice S (P.component s) (D.flow.metric s.1)
    (datum s).pi_two_trivial (datum s).alpha (datum s).nonzero

@[simp] theorem m67SliceFamily_initial
    (S : M59IdentificationSystem.{u})
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0))
    (datum : ∀ s, M67ClassDatum S (P.component s)) :
    m67SliceFamily S initial datum (m67InitialTime P) =
      m67InitialWidthSlice S (P.component (m67InitialTime P)) (D.flow.metric 0) initial := by
  simp [m67SliceFamily]

theorem m67SliceFamily_alpha
    (S : M59IdentificationSystem.{u})
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0))
    (datum : ∀ s, M67ClassDatum S (P.component s))
    (hinit : (datum (m67InitialTime P)).alpha = initial.alpha)
    (s : Set.Icc (0 : ℝ) T) :
    (m67SliceFamily S initial datum s).alpha = (datum s).alpha := by
  classical
  by_cases hs : s = m67InitialTime P
  · subst s
    simpa [m67InitialWidthSlice, m67WidthSliceOfClass] using hinit.symm
  · simp [m67SliceFamily, hs, m67ActualWidthSlice, m67WidthSliceOfClass]

theorem m67SliceFamily_ambient_metric
    (S : M59IdentificationSystem.{u})
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0))
    (datum : ∀ s, M67ClassDatum S (P.component s))
    (s : Set.Icc (0 : ℝ) T) :
    (m67SliceFamily S initial datum s).ambient_metric = D.flow.metric s.1 := by
  classical
  by_cases hs : s = m67InitialTime P
  · subst s
    rw [m67SliceFamily_initial]
    rfl
  · simp [m67SliceFamily, hs, m67ActualWidthSlice, m67WidthSliceOfClass]

theorem m67SliceFamily_identification
    (S : M59IdentificationSystem.{u})
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0))
    (datum : ∀ s, M67ClassDatum S (P.component s))
    (s : Set.Icc (0 : ℝ) T) :
    (m67SliceFamily S initial datum s).loop_pi_three =
      (S.core (P.component s).compact (P.component s).connected
        (P.component s).basepoint (m67SliceFamily S initial datum s).pi_two_trivial).pi_two_pi_three := by
  classical
  by_cases hs : s = m67InitialTime P
  · subst s
    simp [m67InitialWidthSlice, m67WidthSliceOfClass]
  · simp [m67SliceFamily, hs, m67ActualWidthSlice, m67WidthSliceOfClass]

end PoincareConjecture
