import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.LocalDisks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMotion
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)




theorem exists_moved_finite_sphere_system_clipped_disk_neighborhood
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (J P A : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target)
    (hPs : P.space = Q '' ((⋃ i, S i) ∩ Q.source) ∩ J.space)
    {Z : Set V3} {ε : ℝ} (H : PLCarrierMotion J.space Z ε)
    (hAs : A.space = H.map 1 '' P.space)
    {w : V3} (hw : w ∈ A.space) (hwJ : w ∈ interior J.space) :
    ∃ d q : Set V3, IsFinitePLBallPair V2 d q ∧ d ⊆ A.space ∧
      w ∈ d \ q ∧ IsOpen ((Subtype.val : A.space → V3) ⁻¹' (d \ q)) := by
  have hback (y : V3) (hy : y ∈ A.space) : (H.map 1).symm y ∈ P.space := by
    obtain ⟨x, hx, rfl⟩ := hAs.subset hy
    simpa only [Homeomorph.symm_apply_apply] using hx
  have hwbackJ : (H.map 1).symm w ∈ interior J.space := by
    by_contra hn
    have hfix := H.outside 1 ((H.map 1).symm w) hn
    rw [(H.map 1).apply_symm_apply] at hfix
    exact hn (hfix ▸ hwJ)
  obtain ⟨d, q, hd, hdP, hwd, hopen⟩ :=
    exists_finite_sphere_system_clipped_disk_neighborhood S sS hdisjoint Q hQ J P hJ hJQ
      hPs (hback w hw) hwbackJ
  obtain ⟨F, hF, hFval⟩ := H.finitePL 1
  obtain ⟨f, hf, hfval⟩ := hF
  have hHPL : FinitePiecewiseAffineOn (H.map 1) J.space := hf.congr
    (fun x hx => (hfval ⟨x, hx⟩).symm.trans (hFval ⟨x, hx⟩))
  have hdJ : d ⊆ J.space := hdP.trans (hPs.subset.trans inter_subset_right)
  have himage := hd.image_of_subset hHPL hdJ (H.map 1).injective.injOn
  have hmem (T : Set V3) (y : V3) : y ∈ H.map 1 '' T ↔ (H.map 1).symm y ∈ T := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [Homeomorph.symm_apply_apply] using hx
    · intro hy
      exact ⟨(H.map 1).symm y, hy, (H.map 1).apply_symm_apply y⟩
  refine ⟨H.map 1 '' d, H.map 1 '' q, himage,
    (image_mono hdP).trans hAs.symm.subset,
    ⟨(hmem d w).mpr hwd.1, fun h => hwd.2 ((hmem q w).mp h)⟩, ?_⟩
  let back : A.space → P.space := fun y => ⟨(H.map 1).symm y, hback y y.property⟩
  have hbackcont : Continuous back :=
    ((H.map 1).symm.continuous.comp continuous_subtype_val).subtype_mk _
  have heq : (Subtype.val : A.space → V3) ⁻¹' (H.map 1 '' d \ H.map 1 '' q) =
      back ⁻¹' ((Subtype.val : P.space → V3) ⁻¹' (d \ q)) := by
    ext y
    change ((y : V3) ∈ H.map 1 '' d ∧ (y : V3) ∉ H.map 1 '' q) ↔
      ((H.map 1).symm y ∈ d ∧ (H.map 1).symm y ∉ q)
    rw [hmem, hmem]
  rw [heq]
  exact hopen.preimage hbackcont

end PoincareConjecture.M76

