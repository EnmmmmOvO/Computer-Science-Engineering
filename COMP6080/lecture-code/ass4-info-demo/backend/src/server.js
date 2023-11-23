import fs from 'fs';
import express from 'express';
import swaggerUi from 'swagger-ui-express';
import bodyParser from 'body-parser';
import cors from 'cors';
import morgan from 'morgan';

import { InputError, AccessError } from './error';
import swaggerDocument from '../swagger.json';
import {
  getEmailFromAuthorization,
  login,
  logout,
  register,
  save,
  assertOwnsListing,
  assertOwnsBooking,
  addListing,
  getListingDetails,
  getAllListings,
  updateListing,
  removeListing,
  publishListing,
  unpublishListing,
  leaveListingReview,
  makeNewBooking,
  getAllBookings,
  removeBooking,
  acceptBooking,
  declineBooking,
} from './service';

const app = express();

app.use(cors());
app.use(bodyParser.urlencoded({ extended: true }));
app.use(bodyParser.json({ limit: '50mb' }));
app.use(morgan(':method :url :status'));

const catchErrors = (fn) => async (req, res) => {
  try {
    console.log(`Authorization header is ${req.header('Authorization')}`);
    if (req.method === 'GET') {
      console.log(`Query params are ${JSON.stringify(req.params)}`);
    } else {
      console.log(`Body params are ${JSON.stringify(req.body)}`);
    }
    await fn(req, res);
    save();
  } catch (err) {
    if (err instanceof InputError) {
      res.status(400).send({ error: err.message });
    } else if (err instanceof AccessError) {
      res.status(403).send({ error: err.message });
    } else {
      console.log(err);
      res.status(500).send({ error: 'A system error ocurred' });
    }
  }
};

/***************************************************************
                       User Auth Functions
***************************************************************/

const authed = (fn) => async (req, res) => {
  const email = getEmailFromAuthorization(req.header('Authorization'));
  await fn(req, res, email);
};

app.post(
  '/user/auth/login',
  catchErrors(async (req, res) => {
    const { email, password } = req.body;
    const token = await login(email, password);
    return res.json({ token });
  }),
);

app.post(
  '/user/auth/register',
  catchErrors(async (req, res) => {
    const { email, password, name } = req.body;
    const token = await register(email, password, name);
    return res.json({ token });
  }),
);

app.post(
  '/user/auth/logout',
  catchErrors(
    authed(async (req, res, email) => {
      await logout(email);
      return res.json({});
    }),
  ),
);

/***************************************************************
                       Listing Functions
***************************************************************/

app.get(
  '/listings',
  catchErrors(async (req, res) => {
    return res.json({ listings: await getAllListings() });
  }),
);

app.get(
  '/listings/:listingid',
  catchErrors(async (req, res) => {
    const { listingid } = req.params;
    return res.status(200).json({ listing: await getListingDetails(listingid) });
  }),
);

app.post(
  '/listings/new',
  catchErrors(
    authed(async (req, res, email) => {
      const { title, address, price, thumbnail, metadata } = req.body;
      return res.status(200).json({
        listingId: await addListing(title, email, address, price, thumbnail, metadata),
      });
    }),
  ),
);

app.put(
  '/listings/:listingid',
  catchErrors(
    authed(async (req, res, email) => {
      const { listingid } = req.params;
      const { title, address, thumbnail, price, metadata } = req.body;
      await assertOwnsListing(email, listingid);
      await updateListing(listingid, title, address, thumbnail, price, metadata);
      return res.status(200).send({});
    }),
  ),
);

app.delete(
  '/listings/:listingid',
  catchErrors(
    authed(async (req, res, email) => {
      const { listingid } = req.params;
      await assertOwnsListing(email, listingid);
      await removeListing(listingid);
      return res.status(200).send({});
    }),
  ),
);

app.put(
  '/listings/publish/:listingid',
  catchErrors(
    authed(async (req, res, email) => {
      const { listingid } = req.params;
      const { availability } = req.body;
      await assertOwnsListing(email, listingid);
      await publishListing(listingid, availability);
      return res.status(200).send({});
    }),
  ),
);

app.put(
  '/listings/unpublish/:listingid',
  catchErrors(
    authed(async (req, res, email) => {
      const { listingid } = req.params;
      await assertOwnsListing(email, listingid);
      await unpublishListing(listingid);
      return res.status(200).send({});
    }),
  ),
);

app.put(
  '/listings/:listingid/review/:bookingid',
  catchErrors(
    authed(async (req, res, email) => {
      const { listingid, bookingid } = req.params;
      const { review } = req.body;
      await leaveListingReview(email, listingid, bookingid, review);
      return res.status(200).send({});
    }),
  ),
);

/***************************************************************
                       Booking Functions
***************************************************************/

app.get(
  '/bookings',
  catchErrors(
    authed(async (req, res, email) => {
      return res.status(200).json({
        bookings: await getAllBookings(),
      });
    }),
  ),
);

app.delete(
  '/bookings/:bookingid',
  catchErrors(
    authed(async (req, res, email) => {
      const { bookingid } = req.params;
      await assertOwnsBooking(email, bookingid);
      await removeBooking(bookingid);
      return res.status(200).send({});
    }),
  ),
);

app.post(
  '/bookings/new/:listingid',
  catchErrors(
    authed(async (req, res, email) => {
      const { listingid } = req.params;
      const { dateRange, totalPrice } = req.body;
      return res.status(200).json({
        bookingId: await makeNewBooking(email, dateRange, totalPrice, listingid),
      });
    }),
  ),
);

app.put(
  '/bookings/accept/:bookingid',
  catchErrors(
    authed(async (req, res, email) => {
      const { bookingid } = req.params;
      await acceptBooking(email, bookingid);
      return res.status(200).json({});
    }),
  ),
);

app.put(
  '/bookings/decline/:bookingid',
  catchErrors(
    authed(async (req, res, email) => {
      const { bookingid } = req.params;
      await declineBooking(email, bookingid);
      return res.status(200).json({});
    }),
  ),
);

/***************************************************************
                       Running Server
***************************************************************/

app.get('/', (req, res) => res.redirect('/docs'));

app.use('/docs', swaggerUi.serve, swaggerUi.setup(swaggerDocument));

const configData = JSON.parse(fs.readFileSync('../frontend/src/config.json'));
const port = 'BACKEND_PORT' in configData ? configData.BACKEND_PORT : 5033;

const server = app.listen(port, () => {
  console.log(`Backend is now listening on port ${port}!`);
  console.log(`For API docs, navigate to http://localhost:${port}`);
});

export default server;
