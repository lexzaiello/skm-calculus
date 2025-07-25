use super::ast::Expr;
use crate::SKM;

pub fn eval(e: Expr) -> Expr {
    let e2 = match e {
        Expr::Call(lhs, rhs) => {
	    match lhs {
		Expr::Call(lhs_inner, rhs_inner) => {
		    match lhs_inner {
			Expr::K => {
			    rhs_inner
			},
			Expr::Call(lhs_inner_inner, rhs_inner_inner) => {
			    match lhs_inner_inner {
				Expr::S => 
			    }
			}
		    }
		},
		x => x
	    }
	},
        x => x,
    };

    if e2 == e {
        e
    } else {
        eval(e2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_identity() {
        assert_eq!(eval(SKM![(((S K) K) K)]) SKM![K]);
    }
}
