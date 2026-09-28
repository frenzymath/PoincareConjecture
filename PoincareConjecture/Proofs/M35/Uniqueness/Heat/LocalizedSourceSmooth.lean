import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSpatialCoefficientJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.LocalizedDivergence









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure X)

theorem continuous_localizedDivergenceSource {ι : Type*} [TopologicalSpace ι]
    (K : Set X) (A : ι → Fin n → Fin n → 𝓢(X, ℝ)) (χ : 𝓢(X, ℝ))
    (u : ι → dirichletForm K) (G : ι → L2)
    (hA : ∀ i j, Continuous (fun s => schwartzMultiplier (A s i j)))
    (hdA : ∀ i j, Continuous (fun s => schwartzMultiplier
      (∂_{EuclideanSpace.single j (1 : ℝ)} (A s i j))))
    (hu : Continuous u) (hG : Continuous G) :
    Continuous (fun s => localizedDivergenceSource K (A s) χ (u s) (G s)) := by
  have hvalue : Continuous (fun s => (dirichletInclusion K (u s) : L2)) :=
    ((dirichletValue K).subtypeL.comp (dirichletInclusion K)).continuous.comp hu
  have hpartial (i : Fin n) : Continuous (fun s => dirichletPartial K i (u s)) :=
    (dirichletPartial K i).continuous.comp hu
  have hterm (i j : Fin n) : Continuous (fun s =>
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} χ)
        (schwartzMultiplier (A s i j) (dirichletPartial K i (u s))) +
      (schwartzMultiplier (schwartzProduct (A s i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ))
        (dirichletPartial K j (u s)) +
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
        (schwartzProduct (A s i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ)))
        (dirichletInclusion K (u s) : L2))) := by
    have hfirst :=
      (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} χ)).continuous.comp
        ((hA i j).clm_apply (hpartial i))
    have hsecond := (hA i j).clm_apply
      ((schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ)).continuous.comp (hpartial j))
    have hthird := ((hA i j).clm_apply
      ((schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
        (∂_{EuclideanSpace.single i (1 : ℝ)} χ))).continuous.comp hvalue)).add
      ((hdA i j).clm_apply
        ((schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ)).continuous.comp hvalue))
    have hproduct (s : ι) (v : L2) :
        schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
          (schwartzProduct (A s i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ))) v =
        schwartzMultiplier (A s i j)
          (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
            (∂_{EuclideanSpace.single i (1 : ℝ)} χ)) v) +
        schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A s i j))
          (schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ) v) := by
      rw [lineDeriv_schwartzProduct]
      change schwartzMultiplierLinear (_ + _) v = _
      rw [map_add, add_apply]
      change schwartzMultiplier _ v + schwartzMultiplier _ v = _
      rw [schwartzMultiplier_product, schwartzMultiplier_product]
    simpa only [schwartzMultiplier_product, hproduct, Function.comp_def, Pi.add_def]
      using! hfirst.add (hsecond.add hthird)
  exact ((schwartzMultiplier χ).continuous.comp hG).sub
    (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => hterm i j)

theorem contDiffAt_localizedDivergenceSource
    (K : Set X) (A : ℝ → Fin n → Fin n → 𝓢(X, ℝ)) (χ : 𝓢(X, ℝ))
    (u : ℝ → dirichletForm K) (G : ℝ → L2) {t : ℝ} {r : ℕ∞ω}
    (hA : ∀ i j, ContDiffAt ℝ r (fun s => schwartzMultiplier (A s i j)) t)
    (hdA : ∀ i j, ContDiffAt ℝ r (fun s => schwartzMultiplier
      (∂_{EuclideanSpace.single j (1 : ℝ)} (A s i j))) t)
    (hu : ContDiffAt ℝ r u t) (hG : ContDiffAt ℝ r G t) :
    ContDiffAt ℝ r (fun s => localizedDivergenceSource K (A s) χ (u s) (G s)) t := by
  have hvalue : ContDiffAt ℝ r (fun s => (dirichletInclusion K (u s) : L2)) t :=
    ((dirichletValue K).subtypeL.comp (dirichletInclusion K)).contDiff.contDiffAt.comp t hu
  have hpartial (i : Fin n) : ContDiffAt ℝ r (fun s => dirichletPartial K i (u s)) t :=
    (dirichletPartial K i).contDiff.contDiffAt.comp t hu
  have hterm (i j : Fin n) : ContDiffAt ℝ r (fun s =>
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} χ)
        (schwartzMultiplier (A s i j) (dirichletPartial K i (u s))) +
      (schwartzMultiplier (schwartzProduct (A s i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ))
        (dirichletPartial K j (u s)) +
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
        (schwartzProduct (A s i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ)))
        (dirichletInclusion K (u s) : L2))) t := by
    have hfirst :=
      (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} χ)).contDiff.contDiffAt.comp t
        ((hA i j).clm_apply (hpartial i))
    have hsecond := (hA i j).clm_apply
      ((schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ)).contDiff.contDiffAt.comp t
        (hpartial j))
    have hthird := ((hA i j).clm_apply
      ((schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
        (∂_{EuclideanSpace.single i (1 : ℝ)} χ))).contDiff.contDiffAt.comp t hvalue)).add
      ((hdA i j).clm_apply
        ((schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ)).contDiff.contDiffAt.comp t
          hvalue))
    have hproduct (s : ℝ) (v : L2) :
        schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
          (schwartzProduct (A s i j) (∂_{EuclideanSpace.single i (1 : ℝ)} χ))) v =
        schwartzMultiplier (A s i j)
          (schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)}
            (∂_{EuclideanSpace.single i (1 : ℝ)} χ)) v) +
        schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A s i j))
          (schwartzMultiplier (∂_{EuclideanSpace.single i (1 : ℝ)} χ) v) := by
      rw [lineDeriv_schwartzProduct]
      change schwartzMultiplierLinear (_ + _) v = _
      rw [map_add, add_apply]
      change schwartzMultiplier _ v + schwartzMultiplier _ v = _
      rw [schwartzMultiplier_product, schwartzMultiplier_product]
    simpa only [schwartzMultiplier_product, hproduct, Function.comp_apply]
      using hfirst.add (hsecond.add hthird)
  exact ((schwartzMultiplier χ).contDiff.contDiffAt.comp t hG).sub
    (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => hterm i j)

end PoincareConjecture.M35.Uniqueness.Heat
