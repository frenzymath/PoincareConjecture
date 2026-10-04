import PoincareLib.Geometry.Riemannian.Normalization.Connection.Existence
import PoincareLib.Geometry.Riemannian.Normalization.Curvature.Bound
import PoincareLib.Geometry.Riemannian.Curvature.SecondBianchi

/-! Source-name facade for the normalization and metric-compatibility suppliers. -/

namespace PoincareMT

alias m01_exists_leviCivitaData := normalization_exists_leviCivitaData
alias m01_riemannEvaluation_uniform_bound := normalization_riemannEvaluation_uniform_bound
alias LeviCivitaData.horizon_mvfderiv_inner := LeviCivitaData.mvfderiv_inner

end PoincareMT
