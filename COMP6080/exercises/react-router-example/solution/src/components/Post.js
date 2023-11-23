import { Link, useParams } from "react-router-dom";
import jeffsum from "jeffsum";

const Post = () => {
  // Get the ID from the useParams hook
  const { id } = useParams();

  // Create some placeholder text from http://jeffsum.com/
  // Use the id as the number of sentences
  // Note: this isn't needed, it's just a bit of fun :)
  const words = jeffsum(id, "sentences");

  return (
    <>
      {/* Display the post ID */}
      <h1>Random Post #{id}!</h1>
      <Link to="/"> Go Home</Link>
      <p style={{ padding: 20 }}>{words}</p>
    </>
  );
};

export default Post;
