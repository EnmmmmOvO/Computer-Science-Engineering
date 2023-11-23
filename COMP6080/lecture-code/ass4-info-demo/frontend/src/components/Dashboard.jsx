import React from 'react';
import { useNavigate } from 'react-router-dom';

function Dashboard (props) {
  const navigate = useNavigate();

  React.useEffect(() => {
    if (!props.token) {
      navigate('/login');
    }
  }, [props.token]);

  return (
    <>
      Dashboard!
    </>
  )
};

export default Dashboard;