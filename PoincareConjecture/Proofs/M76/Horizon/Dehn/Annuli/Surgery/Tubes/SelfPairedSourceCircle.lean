import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.SelectedComponent
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SelfPairedSourceCircle



set_option autoImplicit false
open Set Metric Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → X} {S : Set E}

local notation "I01" => Icc (0 : ℝ) 1




theorem SourceCircleDecomposition.exists_selfpaired_twofold_source_arcs
    (M : SourceCircleDecomposition f S)
    (i : M.Index) (hself : M.mate i = i) :
    ∃ (a b : E) (U V : Set E) (alpha : I01 ≃ₜ U) (beta : I01 ≃ₜ V),
      a ≠ b ∧ IsFinitePLBallPair ℝ U {a, b} ∧ IsFinitePLBallPair ℝ V {a, b} ∧
      U ∪ V = M.pieces i ∧ U ∩ V = {a, b} ∧
      alpha.IsFinitePL ∧ beta.IsFinitePL ∧
      (alpha 0 : E) = a ∧ (alpha 1 : E) = b ∧
      (beta 0 : E) = b ∧ (beta 1 : E) = a ∧
      (∀ u : I01, ∃ hx : (alpha u : E) ∈ M.graph.space,
        (beta u : E) = (M.partner ⟨alpha u, hx⟩ : E)) ∧
      (∀ u : I01, f (alpha u) = f (beta u)) ∧
      (∀ u v : I01, f (alpha u) = f (alpha v) ↔
        u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)) ∧
      f '' U = f '' M.pieces i ∧ f '' V = f '' M.pieces i := by
  classical
  let P := M.polygon i
  have hPi : Function.Injective P := (M.model i).1
  have hP : P.HasSimplicialEdges := (M.model i).2.1
  have hPs : P.boundary ℝ = M.pieces i := rfl
  obtain ⟨p, hp, hpval⟩ := M.partnerPL
  have hsub : M.pieces i ⊆ M.graph.space := fun _ hx ↦
    M.space.symm.subset (M.piece_subset_double i hx)
  have hpval' (x : E) (hx : x ∈ M.graph.space) :
      p x = (M.partner ⟨x, hx⟩ : E) := (hpval ⟨x, hx⟩).symm
  have hpM : MapsTo p (M.pieces i) (M.pieces i) := by
    intro x hx
    rw [hpval' x (hsub hx)]
    have hmem : (M.partner ⟨x, hsub hx⟩ : E) ∈ M.pieces (M.mate i) :=
      (M.partner_component i ⟨x, hsub hx⟩).mp hx
    exact hself ▸ hmem
  have hinv (x : E) (hx : x ∈ M.pieces i) : p (p x) = x := by
    calc
      p (p x) = p (M.partner ⟨x, hsub hx⟩) := congrArg p (hpval' x (hsub hx))
      _ = (M.partner (M.partner ⟨x, hsub hx⟩) : E) := (hpval _).symm
      _ = x := congrArg Subtype.val (M.involutive ⟨x, hsub hx⟩)
  have hfree (x : E) (hx : x ∈ M.pieces i) : p x ≠ x := by
    rw [hpval' x (hsub hx)]
    exact M.free ⟨x, hsub hx⟩
  obtain ⟨a, ha⟩ := (M.pieces_isConnected i).nonempty
  let b := p a
  have hb : b ∈ M.pieces i := hpM ha
  have hab : a ≠ b := (hfree a ha).symm
  obtain ⟨U, V, hU, hV, hUV, hinter⟩ := P.exists_arcs_at_marks hP hPi
    (hPs.symm ▸ ha) (hPs.symm ▸ hb) hab
  have hcover : U ∪ V = M.pieces i := hUV.trans hPs
  have hUG : U ⊆ M.graph.space := subset_union_left.trans (hcover.subset.trans hsub)
  have hVG : V ⊆ M.graph.space := subset_union_right.trans (hcover.subset.trans hsub)
  have hswap : p '' U = V ∧ p '' V = U := freeInvolution_exchanges_circle_arcs
    hU hV hab hinter (hp.continuousOn.mono (hcover.subset.trans hsub))
    (by simpa only [hcover] using hpM) (by simpa only [hcover] using hinv)
    (by simpa only [hcover] using hfree) rfl (hinv a ha)
  have hmem (x : M.graph.space) :
      (x : E) ∈ U ↔ (M.partner x : E) ∈ V := by
    rw [← hpval' x x.property]
    constructor
    · intro hx
      exact hswap.1.subset ⟨x, hx, rfl⟩
    · intro hx
      have hpx := hswap.2.subset (mem_image_of_mem p hx)
      have hxx : p (p x) = (x : E) := by
        calc
          p (p x) = p (M.partner x) := congrArg p (hpval x).symm
          _ = (M.partner (M.partner x) : E) := (hpval _).symm
          _ = x := congrArg Subtype.val (M.involutive x)
      exact hxx ▸ hpx
  let d := M.partner.restrictSubsets hUG hVG hmem
  have htri := hU
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := htri
  have hd : d.IsFinitePL := M.partnerPL.restrictSubsets hUG hVG hmem K hK hKs
  obtain ⟨alpha, halpha, ha0, ha1⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  change (alpha (0 : I01) : E) = a at ha0
  change (alpha (1 : I01) : E) = b at ha1
  let beta := alpha.trans d
  have hbeta : beta.IsFinitePL := halpha.trans hd
  have hbetaval (u : I01) : (beta u : E) = p (alpha u) :=
    (hpval' (alpha u) (hUG (alpha u).property)).symm
  have hb0 : (beta 0 : E) = b := by rw [hbetaval, ha0]
  have hb1 : (beta 1 : E) = a := by rw [hbetaval, ha1]; exact hinv a ha
  have hsync (u : I01) : f (alpha u) = f (beta u) :=
    (M.value ⟨alpha u, hUG (alpha u).property⟩).symm
  have hend : f (alpha (0 : I01)) = f (alpha (1 : I01)) := by
    rw [hsync, hb0, ha1]
  have hfib (u v : I01) : f (alpha u) = f (alpha v) ↔
      u = v ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) := by
    constructor
    · intro huv
      by_cases heq : (alpha u : E) = (alpha v : E)
      · exact Or.inl (alpha.injective (Subtype.ext heq))
      · have hvp := M.unique ⟨alpha u, hUG (alpha u).property⟩ (alpha v)
          (M.space.subset (hUG (alpha v).property)).1 heq huv
        have hvV : (alpha v : E) ∈ V := hvp ▸ (hmem ⟨alpha u,
          hUG (alpha u).property⟩).mp (alpha u).property
        rcases hinter.subset ⟨(alpha v).property, hvV⟩ with hv0 | hv1
        · have hv : v = 0 := alpha.injective (Subtype.ext (hv0.trans ha0.symm))
          have hu : u = 1 := by
            have h := congrArg p hvp
            rw [← hpval' (alpha u) (hUG (alpha u).property),
              hinv _ (hcover.subset (Or.inl (alpha u).property)), hv0] at h
            exact alpha.injective (Subtype.ext (h.symm.trans ha1.symm))
          exact Or.inr (Or.inr ⟨hu, hv⟩)
        · have hv : v = 1 := alpha.injective (Subtype.ext (hv1.trans ha1.symm))
          have hu : u = 0 := by
            have h := congrArg p hvp
            rw [← hpval' (alpha u) (hUG (alpha u).property),
              hinv _ (hcover.subset (Or.inl (alpha u).property)), hv1] at h
            have h' : a = (alpha u : E) := (hinv a ha).symm.trans h
            exact alpha.injective (Subtype.ext (h'.symm.trans ha0.symm))
          exact Or.inr (Or.inl ⟨hu, hv⟩)
    · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · exact hend
      · exact hend.symm
  have hphysical : f '' U = f '' V := by
    rw [← hswap.1, image_image]
    apply image_congr
    intro x hx
    rw [hpval' x (hUG hx)]
    exact (M.value ⟨x, hUG hx⟩).symm
  refine ⟨a, b, U, V, alpha, beta, hab, hU, hV, hcover, hinter, halpha, hbeta,
    ha0, ha1, hb0, hb1, fun u => ⟨hUG (alpha u).property, rfl⟩, hsync, hfib, ?_, ?_⟩
  · rw [← hcover, image_union, ← hphysical, union_self]
  · rw [← hcover, image_union, hphysical, union_self]

end PoincareConjecture.M76.Dehn.Annuli
