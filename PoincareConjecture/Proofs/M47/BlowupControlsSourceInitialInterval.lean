import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingCanonical









set_option autoImplicit false

open Set

namespace PoincareConjecture.M47



def standardInitialNeckExtended
    {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
    {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck atlas G v gamma z
      (Icc (-v * (G.connection v).scalarCurvature z) 0))
    (hlong : 1 + gamma ≤ v * (G.connection v).scalarCurvature z) :
    StandardEvolvingNeck atlas G v gamma z (Ioc (-(1 + gamma)) 0) := by
  have hsub : Ioc (-(1 + gamma)) 0 ⊆
      Icc (-v * (G.connection v).scalarCurvature z) 0 := by
    intro u hu
    exact ⟨by linarith only [hlong, hu.1], hu.2⟩
  exact {
    time_mem := N.time_mem
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scalar_pos := N.scalar_pos
    patch := N.patch
    interval_survival := fun u hu => N.interval_survival u (hsub hu)
    close := by
      obtain ⟨hsmooth, B, hB, hjets⟩ := N.close
      exact ⟨fun u hu => hsmooth u (hsub hu), B, hB,
        fun u hu => hjets u (hsub hu)⟩ }

end PoincareConjecture.M47
