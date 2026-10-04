import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.UniquenessData

/-!
# Identifying a partial standard limit

Morgan--Tian, Lemma 16.8 and Corollary 16.9, pp. 372-373, identify the
constructed partial limit by Theorem 12.5. These lemmas apply M35 to that
same initial metric and compare it to an arbitrary maximal model decoration.
The construction and convergence of the partial limit are not assumed here
as consequences of uniqueness.
-/

set_option autoImplicit false

namespace PoincareMT

namespace RepairedStandardCapUniquenessData

variable {g₀ : StandardInitialMetric} {E : RepairedStandardCapExistenceData g₀}
  (U : RepairedStandardCapUniquenessData g₀ E)

include U

/-- Every maximal decoration has the unit lifetime used in Corollary 16.9,
p. 373, by M35's lifetime uniqueness. -/
theorem model_lifetime_one (G : MaximalStandardCapFlow g₀) : G.base.lifetime = 1 :=
  (U.unique_lifetime G).symm.trans U.lifetime_one

/-- On the unit time interval the arbitrary maximal model is the
selected M34 model (Lemma 16.8, p. 372). -/
theorem model_metric_eq (G : MaximalStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) : E.flow.metric t = G.metric t := by
  apply U.unique_metric G t
  simpa only [U.lifetime_one, U.model_lifetime_one G, Set.inter_self] using ht

/-- A genuine partial limit agrees with the selected standard solution on
the common time interval (Lemma 16.8, p. 372). -/
theorem partial_metric_eq (G : PartialStandardCapFlow g₀)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (hG : t < G.lifetime) :
    G.flow.metric t = E.flow.metric t := by
  symm
  apply U.partial_unique_metric G t
  exact ⟨by simpa only [U.lifetime_one] using ht, ht.1, hG⟩

/-- After partial-limit identification, the limit may be compared to the
observation's maximal model (Corollary 16.9, p. 373). -/
theorem partial_metric_eq_model (G : PartialStandardCapFlow g₀)
    (S : MaximalStandardCapFlow g₀) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) (hG : t < G.lifetime) :
    G.flow.metric t = S.metric t :=
  (U.partial_metric_eq G ht hG).trans (U.model_metric_eq S ht)

end RepairedStandardCapUniquenessData

end PoincareMT
