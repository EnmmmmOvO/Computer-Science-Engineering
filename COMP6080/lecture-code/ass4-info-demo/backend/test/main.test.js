import request from 'supertest';
import server from '../src/server';
import { reset } from '../src/service';

const THUMBNAIL =
  'data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAUAAAAFCAYAAACNbyblAAAAHElEQVQI12P4//8/w38GIAXDIBKE0DHxgljNBAAO9TXL0Y4OHwAAAABJRU5ErkJggg==';

const USER1 = {
  email: 'marina@airbrb.com',
  name: 'Marina',
  password: 'p@ssword123',
};

const USER2 = {
  email: 'mariya@airbrb.com',
  name: 'Mariya',
  password: 'p@ssword123',
};

const LISTING1 = {
  title: 'House1',
  address: {
    string1: 'Street1',
    string2: 'Street1',
    string3: 'Street1',
  },
  price: 250,
  thumbnail: THUMBNAIL,
  metadata: {
    property1: 'Penthouse',
    property2: ['Air Conditioning', 'Balcony'],
    property3: 2,
  },
};

const LISTING2 = {
  title: 'House2',
  address: {
    string1: 'Street2',
    string2: 'Street2',
    string3: 'Street2',
  },
  price: '300',
  thumbnail: THUMBNAIL,
  metadata: {
    property1: 'House',
    property2: ['Two Monitors', 'Light-up Keyboard'],
    property3: 2,
  },
};

const LISTING3 = {
  title: 'House3',
  address: {
    string1: 'Street3',
    string2: 'Street3',
    string3: 'Street3',
  },
  price: 250,
  thumbnail: 'thumbnail2',
  metadata: {
    property1: 'villa',
    property2: ['Terrace', 'Garden'],
    property3: 3,
  },
};

const postTry = async (path, status, payload, token) => sendTry('post', path, status, payload, token);
const getTry = async (path, status, payload, token) => sendTry('get', path, status, payload, token);
const deleteTry = async (path, status, payload, token) => sendTry('delete', path, status, payload, token);
const putTry = async (path, status, payload, token) => sendTry('put', path, status, payload, token);

const sendTry = async (typeFn, path, status = 200, payload = {}, token = null) => {
  let req = request(server);
  if (typeFn === 'post') {
    req = req.post(path);
  } else if (typeFn === 'get') {
    req = req.get(path);
  } else if (typeFn === 'delete') {
    req = req.delete(path);
  } else if (typeFn === 'put') {
    req = req.put(path);
  }
  if (token !== null) {
    req = req.set('Authorization', `Bearer ${token}`);
  }
  const response = await req.send(payload);
  expect(response.statusCode).toBe(status);
  return response.body;
};

const validToken = async (user) => {
  const { token } = await postTry('/user/auth/login', 200, {
    email: user.email,
    password: user.password,
  });
  return token;
};

const singleListingId = async () => {
  const { listings } = await getTry('/listings', 200, {});
  return listings[0].id;
};

const singleBookingId = async () => {
  const { bookings } = await getTry('/bookings', 200, {}, await validToken(USER1));
  return bookings[0].id;
};

describe('Test the root path', () => {
  beforeAll(() => {
    reset();
  });

  beforeAll(() => {
    server.close();
  });

  /***************************************************************
                       Auth Tests
  ***************************************************************/
  describe('Sign Up and Log In', () => {
    test('Registration of initial user', async () => {
      const body = await postTry('/user/auth/register', 200, {
        email: USER1.email,
        password: USER1.password,
        name: USER1.name,
      });
      expect(body.token instanceof String);
    });

    test('Registration of secondary user', async () => {
      const body = await postTry('/user/auth/register', 200, {
        email: USER2.email,
        password: USER2.password,
        name: USER2.name,
      });
      expect(body.token instanceof String);
    });

    test('Inability to re-register a user', async () => {
      await postTry('/user/auth/register', 400, {
        email: USER1.email,
        password: USER1.password,
        name: USER1.name,
      });
    });

    test('Login to an existing user', async () => {
      const body = await postTry('/user/auth/login', 200, {
        email: USER1.email,
        password: USER1.password,
      });
      expect(body.token instanceof String);
    });

    test('Login attempt with invalid credentials 1', async () => {
      await postTry('/user/auth/login', 400, {
        email: 'hayden.smith@unsw.edu.a',
        password: 'bananapie',
      });
    });

    test('Login attempt with invalid credentials 2', async () => {
      await postTry('/user/auth/login', 400, {
        email: 'hayden.smith@unsw.edu.au',
        password: 'bananapi',
      });
    });

    test('Logout a valid session', async () => {
      const bodyLogout = await postTry('/user/auth/logout', 200, {}, await validToken(USER1));
      expect(bodyLogout).toMatchObject({});
    });

    test('Logout a session without auth token', async () => {
      const body = await postTry('/user/auth/logout', 403, {});
      expect(body).toMatchObject({});
    });
  });

  /***************************************************************
                       Listing Tests
  ***************************************************************/

  describe('Creating a single listing', () => {
    test('Initially there are no listings', async () => {
      const body = await getTry('/listings', 200, {});
      expect(body.listings).toHaveLength(0);
    });

    test('Creating a single listing', async () => {
      await postTry(
        '/listings/new',
        200,
        {
          title: LISTING1.title,
          address: LISTING1.address,
          price: LISTING1.price,
          thumbnail: LISTING1.thumbnail,
          metadata: LISTING1.metadata,
        },
        await validToken(USER1),
      );
    });

    test('Creating a single listing, duplicate title', async () => {
      await postTry(
        '/listings/new',
        400,
        {
          title: LISTING1.title,
          address: LISTING1.address,
          price: LISTING1.price,
          thumbnail: LISTING1.thumbnail,
          metadata: LISTING1.metadata,
        },
        await validToken(USER1),
      );
    });

    test('That there is now one listing', async () => {
      const body = await getTry('/listings', 200, {});
      const listingid = body.listings[0].id;
      expect(body.listings).toHaveLength(1);
      expect(typeof body.listings[0].id).toBe('number');
      expect(body.listings[0].title).toBe(LISTING1.title);
      expect(body.listings[0].owner).toBe(USER1.email);
      expect(body.listings[0].address).toMatchObject(LISTING1.address);
      expect(body.listings[0].thumbnail).toBe(THUMBNAIL);
      expect(body.listings[0].price).toBe(LISTING1.price);
      expect(body.listings[0].reviews).toMatchObject([]);

      const details = await getTry(`/listings/${listingid}`, 200, {});
      expect(details.listing.metadata).toMatchObject(LISTING1.metadata);
      expect(details.listing.availability).toMatchObject([]);
      expect(details.listing.published).toBe(false);
    });
  });

  /***************************************************************
                       Failing to Create Listings
  ***************************************************************/

  describe('Creating a single listing - FAIL CASES', () => {
    test('Creating a single listing, value missing', async () => {
      await postTry('/listings/new', 400, {}, await validToken(USER1));
    });

    test('Creating a single listing, token missing', async () => {
      await postTry('/listings/new', 403, {
        title: 'LISTING',
        address: 'ADDRESS',
        price: 200,
        thumbnail: THUMBNAIL,
        metadata: { something: 'here' },
      });
    });

    test('Creating a single listing, no title', async () => {
      await postTry(
        '/listings/new',
        400,
        {
          address: 'ADDRESS',
          price: 200,
          thumbnail: THUMBNAIL,
          metadata: { something: 'here' },
        },
        await validToken(USER1),
      );
    });

    test('Creating a single listing, no address', async () => {
      await postTry(
        '/listings/new',
        400,
        {
          title: 'LISTING',
          price: 200,
          thumbnail: THUMBNAIL,
          metadata: { something: 'here' },
        },
        await validToken(USER1),
      );
    });

    test('Creating a single listing, no price', async () => {
      await postTry(
        '/listings/new',
        400,
        {
          title: 'LISTING',
          address: 'ADDRESS',
          thumbnail: THUMBNAIL,
          metadata: { something: 'here' },
        },
        await validToken(USER1),
      );
    });

    test('Creating a single listing, non-numerical price', async () => {
      await postTry(
        '/listings/new',
        400,
        {
          title: 'LISTING',
          address: 'ADDRESS',
          price: 'PRICE',
          thumbnail: THUMBNAIL,
          metadata: { something: 'here' },
        },
        await validToken(USER1),
      );
    });

    test('Creating a single listing, no thumbnail', async () => {
      await postTry(
        '/listings/new',
        400,
        {
          title: 'LISTING',
          address: 'ADDRESS',
          price: '200',
          metadata: { something: 'here' },
        },
        await validToken(USER1),
      );
    });

    test('Creating a single listing, no property metadata', async () => {
      await postTry(
        '/listings/new',
        400,
        {
          title: 'LISTING',
          address: 'ADDRESS',
          price: '200',
          thumbnail: THUMBNAIL,
        },
        await validToken(USER1),
      );
    });
  });

  /***************************************************************
                       Creating a Second Listing
  ***************************************************************/

  describe('Creating a secondary listing', () => {
    test('Create a second listing', async () => {
      await postTry(
        '/listings/new',
        200,
        {
          title: LISTING2.title,
          address: LISTING2.address,
          price: LISTING2.price,
          thumbnail: LISTING2.thumbnail,
          metadata: LISTING2.metadata,
        },
        await validToken(USER1),
      );
    });

    test('That there is now two listings', async () => {
      const body = await getTry('/listings', 200, {});
      expect(body.listings).toHaveLength(2);
    });
  });

  /***************************************************************
                       Deleting Listing
  ***************************************************************/

  describe('Deleting a listing', () => {
    test('Try and delete a listing with invalid token', async () => {
      const { listings } = await getTry('/listings', 200, {});
      const listingid = listings[1].id;
      await deleteTry(`/listings/${listingid}`, 403, {});
    });

    test('Try and delete a listing with invalid listingid', async () => {
      await deleteTry(`/listings/${99999999999999}`, 400, {}, await validToken(USER1));
    });

    test('Try and delete a listing', async () => {
      const { listings } = await getTry('/listings', 200, {});
      const listingid = listings[1].id;
      await deleteTry(`/listings/${listingid}`, 200, {}, await validToken(USER1));
    });

    test('That there is now one listing again', async () => {
      const body = await getTry('/listings', 200, {});
      expect(body.listings).toHaveLength(1);
    });
  });

  /***************************************************************
                       Updating Listing
  ***************************************************************/

  describe('Updating a listing address', () => {
    test('Update listing address', async () => {
      const listingid = await singleListingId();
      await putTry(
        `/listings/${listingid}`,
        200,
        {
          address: LISTING3.address,
        },
        await validToken(USER1),
      );
    });

    test('Check that address updated', async () => {
      const listingid = await singleListingId();
      const { listing } = await getTry(`/listings/${listingid}`, 200, {});

      expect(listing.address).toMatchObject(LISTING3.address);
    });
  });

  describe('Updating a listing title and price', () => {
    test('Update listing title and price', async () => {
      const listingid = await singleListingId();
      await putTry(
        `/listings/${listingid}`,
        200,
        {
          title: 'House3',
          price: 250,
        },
        await validToken(USER1),
      );
    });

    test('Check that title and price updated', async () => {
      const listingid = await singleListingId();
      const { listing } = await getTry(`/listings/${listingid}`, 200, {});

      expect(listing.title).toBe(LISTING3.title);
      expect(listing.price).toBe(LISTING3.price);
    });
  });

  describe('Updating a listing thumbnail and metadata', () => {
    test('Update listing thumbnail and metadata', async () => {
      const listingid = await singleListingId();
      await putTry(
        `/listings/${listingid}`,
        200,
        {
          thumbnail: LISTING3.thumbnail,
          metadata: LISTING3.metadata,
        },
        await validToken(USER1),
      );
    });

    test('Check that thumbnail and metadata updated', async () => {
      const listingid = await singleListingId();
      const { listing } = await getTry(`/listings/${listingid}`, 200, {});

      expect(listing.metadata).toMatchObject(LISTING3.metadata);
      expect(listing.thumbnail).toBe(LISTING3.thumbnail);
    });
  });

  /***************************************************************
                       Publish Listing
  ***************************************************************/

  describe('Publishing a listing', () => {
    test('Try publishing a listing without availability', async () => {
      const listingid = await singleListingId();
      await putTry(`/listings/publish/${listingid}`, 400, {}, await validToken(USER1));
    });

    test('Publish a listing', async () => {
      const listingid = await singleListingId();
      await putTry(
        `/listings/publish/${listingid}`,
        200,
        {
          availability: [
            { from: 'date1', to: 'date2' },
            { from: 'date3', to: 'date4' },
          ],
        },
        await validToken(USER1),
      );
    });

    test('Check that a listing has been published', async () => {
      const listingid = await singleListingId();
      const { listing } = await getTry(`/listings/${listingid}`, 200, {});

      expect(listing.published).toBe(true);
    });
  });

  /***************************************************************
                       Unpublish Listing
  ***************************************************************/

  describe('Unpublish a listing', () => {
    test('Try unpublishing with a fake listingid', async () => {
      const listingid = '12345';
      await putTry(`/listings/unpublish/${listingid}`, 400, {}, await validToken(USER1));
    });

    test('Unpublish a listing', async () => {
      const listingid = await singleListingId();
      await putTry(`/listings/unpublish/${listingid}`, 200, {}, await validToken(USER1));
    });

    test('Check that a listing has been unpublished', async () => {
      const listingid = await singleListingId();
      const { listing } = await getTry(`/listings/${listingid}`, 200, {});

      expect(listing.published).toBe(false);
    });
  });

  /***************************************************************
                       Creating Bookings
  ***************************************************************/

  describe('Creating a single booking', () => {
    beforeAll(async () => {
      // We want to make sure the listing is published
      const listingid = await singleListingId();
      await putTry(
        `/listings/publish/${listingid}`,
        200,
        {
          availability: [
            { from: 'date1', to: 'date2' },
            { from: 'date3', to: 'date4' },
          ],
        },
        await validToken(USER1),
      );
    });

    test('Initially there are no bookings', async () => {
      const body = await getTry('/bookings', 200, {}, await validToken(USER1));
      expect(body.bookings).toHaveLength(0);
    });

    test('Creating a single booking', async () => {
      const listingid = await singleListingId();
      await postTry(
        `/bookings/new/${listingid}`,
        200,
        { dateRange: { from: 'date1', to: 'date2' }, totalPrice: 500 },
        await validToken(USER2),
      );
    });

    test('Check there is now one booking', async () => {
      const body = await getTry('/bookings', 200, {}, await validToken(USER1));

      expect(body.bookings).toHaveLength(1);
      expect(typeof body.bookings[0].id).toBe('number');

      expect(body.bookings[0].totalPrice).toBe(500);
      expect(body.bookings[0].dateRange).toMatchObject({ from: 'date1', to: 'date2' });
    });
  });

  /***************************************************************
                       Failing to Create Bookings
  ***************************************************************/

  describe('Create a booking - FAIL CASES', () => {
    test('Creating a single booking, both values missing', async () => {
      const listingid = await singleListingId();
      await postTry(`/bookings/new/${listingid}`, 400, {}, await validToken(USER1));
    });

    test('Creating a single booking, dateRange is missing', async () => {
      const listingid = await singleListingId();
      await postTry(`/bookings/new/${listingid}`, 400, { totalPrice: 500 }, await validToken(USER1));
    });

    test('Creating a single booking, totalPrice is missing', async () => {
      const listingid = await singleListingId();
      await postTry(
        `/bookings/new/${listingid}`,
        400,
        { dateRange: { from: 'date1', to: 'date2' } },
        await validToken(USER1),
      );
    });

    test('Creating a single booking, totalPrice is a char string', async () => {
      const listingid = await singleListingId();
      await postTry(
        `/bookings/new/${listingid}`,
        400,
        {
          dateRange: { from: 'date1', to: 'date2' },
          totalPrice: 'haha',
        },
        await validToken(USER1),
      );
    });

    test('Creating a single booking, totalPrice is less than 0', async () => {
      const listingid = await singleListingId();
      await postTry(
        `/bookings/new/${listingid}`,
        400,
        {
          dateRange: { from: 'date1', to: 'date2' },
          totalPrice: -1,
        },
        await validToken(USER1),
      );
    });

    test('Creating a single booking, listingid is wrong', async () => {
      const listingid = '123456';
      await postTry(
        `/bookings/new/${listingid}`,
        400,
        { dateRange: { from: 'date1', to: 'date2' }, totalPrice: 500 },
        await validToken(USER1),
      );
    });

    test('Creating a single booking, token missing', async () => {
      const listingid = await singleListingId();
      await postTry(`/bookings/new/${listingid}`, 403, {
        dateRange: { from: 'date1', to: 'date2' },
        totalPrice: 500,
      });
    });

    test('Creating a single booking, listing is unpublished', async () => {
      const body = await postTry(
        '/listings/new',
        200,
        {
          title: 'Unpublished',
          address: LISTING1.address,
          price: LISTING1.price,
          thumbnail: LISTING1.thumbnail,
          metadata: LISTING1.metadata,
        },
        await validToken(USER1),
      );
      const listingid = body.listingId;

      await postTry(
        `/bookings/new/${listingid}`,
        400,
        {
          dateRange: { from: 'date1', to: 'date2' },
          totalPrice: 500,
        },
        await validToken(USER1),
      );
      await deleteTry(`/listings/${listingid}`, 200, {}, await validToken(USER1));
    });

    test('Creating a single booking, listing belongs to the user', async () => {
      const listingid = await singleListingId();
      await postTry(
        `/bookings/new/${listingid}`,
        400,
        { dateRange: { from: 'date1', to: 'date2' }, totalPrice: 500 },
        await validToken(USER1),
      );
    });
  });

  /***************************************************************
                       Creating a Second Booking
  ***************************************************************/

  describe('Creating a secondary booking', () => {
    test('Creating a second booking', async () => {
      const listingid = await singleListingId();
      await postTry(
        `/bookings/new/${listingid}`,
        200,
        { dateRange: { from: 'date3', to: 'date4' }, totalPrice: 700 },
        await validToken(USER2),
      );
    });

    test('Check there is now two bookings', async () => {
      const body = await getTry('/bookings', 200, {}, await validToken(USER1));
      expect(body.bookings).toHaveLength(2);
    });
  });

  /***************************************************************
                       Deleting Bookings
  ***************************************************************/

  describe('Deleting a booking', () => {
    test('Try and delete a booking with invalid token', async () => {
      const bookingid = await singleBookingId();
      await deleteTry(`/bookings/${bookingid}`, 403, {});
    });

    test('Try and delete a booking with invalid bookingid', async () => {
      await deleteTry(`/bookings/${99999999999999}`, 400, {}, await validToken(USER2));
    });

    test('Try and delete a booking', async () => {
      const { bookings } = await getTry('/bookings', 200, {}, await validToken(USER2));
      const bookingid = bookings[1].id;
      await deleteTry(`/bookings/${bookingid}`, 200, {}, await validToken(USER2));
    });

    test('That there is now one listing again', async () => {
      const body = await getTry('/bookings', 200, {}, await validToken(USER2));
      expect(body.bookings).toHaveLength(1);
    });
  });

  /***************************************************************
                       Failing to Accept Bookings
  ***************************************************************/

  describe('Accept a booking - FAIL CASES', () => {
    test('Accepting a booking without a token', async () => {
      const bookingid = await singleBookingId();
      await putTry(`/bookings/accept/${bookingid}`, 403, {});
    });

    test("Accepting a booking by USER1, where listing doesn't belong to USER1", async () => {
      // Creating a listing under USER2
      const body1 = await postTry(
        '/listings/new',
        200,
        {
          title: LISTING1.title,
          address: LISTING1.address,
          price: LISTING1.price,
          thumbnail: LISTING1.thumbnail,
          metadata: LISTING1.metadata,
        },
        await validToken(USER2),
      );

      const listingid = body1.listingId;
      // Publish the listing
      await putTry(
        `/listings/publish/${listingid}`,
        200,
        {
          availability: [
            { from: 'date1', to: 'date2' },
            { from: 'date3', to: 'date4' },
          ],
        },
        await validToken(USER2),
      );
      // Creating a booking from USER1 under USER2 listing
      const body2 = await postTry(
        `/bookings/new/${listingid}`,
        200,
        { dateRange: { from: 'date5', to: 'date6' }, totalPrice: 600 },
        await validToken(USER1),
      );
      const bookingid = body2.bookingId;

      await putTry(`/bookings/accept/${bookingid}`, 400, {}, await validToken(USER1));
      // Clean up
      await deleteTry(`/listings/${listingid}`, 200, {}, await validToken(USER2));
      await deleteTry(`/bookings/${bookingid}`, 200, {}, await validToken(USER1));
    });

    test("Accepting a booking by USER2, where listing doesn't belong to USER2", async () => {
      const bookingid = await singleBookingId();
      await putTry(`/bookings/accept/${bookingid}`, 400, {}, await validToken(USER2));
    });

    test('Accepting a booking with a fake bookingId', async () => {
      const bookingid = '12345';
      await putTry(`/bookings/accept/${bookingid}`, 400, {}, await validToken(USER1));
    });
  });

  /***************************************************************
                       Accepting Bookings
  ***************************************************************/

  describe('Accept a booking', () => {
    test('Accepting a booking by USER1 under USER1 listing', async () => {
      const bookingid = await singleBookingId();
      await putTry(`/bookings/accept/${bookingid}`, 200, {}, await validToken(USER1));
    });

    test("Accepting a booking by USER1 that's been accepted", async () => {
      const bookingid = await singleBookingId();
      await putTry(`/bookings/accept/${bookingid}`, 400, {}, await validToken(USER1));
    });
  });

  /***************************************************************
                       Failing to Decline Bookings
  ***************************************************************/

  describe('Decline a booking - FAIL CASES', () => {
    test('Declining a booking without a token', async () => {
      const bookingid = await singleBookingId();
      await putTry(`/bookings/decline/${bookingid}`, 403, {});
    });

    test('Declining a booking by USER1, where listing belongs to USER2', async () => {
      // Creating a listing under USER2
      const body1 = await postTry(
        '/listings/new',
        200,
        {
          title: LISTING1.title,
          address: LISTING1.address,
          price: LISTING1.price,
          thumbnail: LISTING1.thumbnail,
          metadata: LISTING1.metadata,
        },
        await validToken(USER2),
      );

      const listingid = body1.listingId;
      // Publish the listing
      await putTry(
        `/listings/publish/${listingid}`,
        200,
        {
          availability: [
            { from: 'date1', to: 'date2' },
            { from: 'date3', to: 'date4' },
          ],
        },
        await validToken(USER2),
      );
      // Creating a booking from USER1 under USER2 listing
      const body2 = await postTry(
        `/bookings/new/${listingid}`,
        200,
        { dateRange: { from: 'date5', to: 'date6' }, totalPrice: 600 },
        await validToken(USER1),
      );
      const bookingid = body2.bookingId;

      // Accept the booking by USER2
      await putTry(`/bookings/accept/${bookingid}`, 200, {}, await validToken(USER2));
      // Now try to decline by USER1
      await putTry(`/bookings/accept/${bookingid}`, 400, {}, await validToken(USER1));
      // Clean up
      await deleteTry(`/listings/${listingid}`, 200, {}, await validToken(USER2));
      await deleteTry(`/bookings/${bookingid}`, 200, {}, await validToken(USER1));
    });
  });

  test('Declining a booking by USER2, where listing belongs to USER1', async () => {
    const bookingid = await singleBookingId();
    await putTry(`/bookings/decline/${bookingid}`, 400, {}, await validToken(USER2));
  });

  test('Declining a booking with a fake bookingId', async () => {
    const bookingid = '12345';
    await putTry(`/bookings/decline/${bookingid}`, 400, {}, await validToken(USER1));
  });

  test("Declining a booking that's already been accepted", async () => {
    const bookingid = await singleBookingId();
    await putTry(`/bookings/decline/${bookingid}`, 400, {}, await validToken(USER1));
  });

  /***************************************************************
                       Declining Bookings
  ***************************************************************/

  describe('Decline a booking', () => {
    test('Declining a booking by USER1 under USER1 listing', async () => {
      // create a new booking under USER 2
      const listingid = await singleListingId();
      const body = await postTry(
        `/bookings/new/${listingid}`,
        200,
        { dateRange: { from: 'date3', to: 'date4' }, totalPrice: 700 },
        await validToken(USER2),
      );

      const bookingid = body.bookingId;

      await putTry(`/bookings/decline/${bookingid}`, 200, {}, await validToken(USER1));
      // clean-up
      await deleteTry(`/bookings/${bookingid}`, 200, {}, await validToken(USER2));
    });

    test("Declining a booking by USER1 that's already been declined", async () => {
      // create a new booking under USER 2
      const listingid = await singleListingId();
      const body = await postTry(
        `/bookings/new/${listingid}`,
        200,
        { dateRange: { from: 'date3', to: 'date4' }, totalPrice: 700 },
        await validToken(USER2),
      );

      const bookingid = body.bookingId;

      // decline the booking
      await putTry(`/bookings/decline/${bookingid}`, 200, {}, await validToken(USER1));
      // try declining again
      await putTry(`/bookings/decline/${bookingid}`, 400, {}, await validToken(USER1));

      // clean-up
      await deleteTry(`/bookings/${bookingid}`, 200, {}, await validToken(USER2));
    });

    test("Accepting a booking by USER1 that's already been declined", async () => {
      // create a new booking under USER 2
      const listingid = await singleListingId();
      const body = await postTry(
        `/bookings/new/${listingid}`,
        200,
        { dateRange: { from: 'date3', to: 'date4' }, totalPrice: 700 },
        await validToken(USER2),
      );

      const bookingid = body.bookingId;

      // decline the booking
      await putTry(`/bookings/decline/${bookingid}`, 200, {}, await validToken(USER1));
      // try accepting the booking
      await putTry(`/bookings/accept/${bookingid}`, 400, {}, await validToken(USER1));

      // clean-up
      await deleteTry(`/bookings/${bookingid}`, 200, {}, await validToken(USER2));
    });
  });

  /***************************************************************
                       Listing Reviews
  ***************************************************************/

  describe('Publishing a listing review - FAIL CASES', () => {
    test('Try publishing a listing review with no token', async () => {
      const listingid = await singleListingId();
      const bookingid = await singleBookingId();
      const review = { text: 'Great Place!', rating: 5 };
      await putTry(`/listings/${listingid}/review/${bookingid}`, 403, review);
    });

    test('Try publishing a listing review with a fake bookingid', async () => {
      const listingid = await singleListingId();
      const bookingid = '123456';
      const review = { text: 'Great Place!', rating: 5 };
      await putTry(`/listings/${listingid}/review/${bookingid}`, 400, review, await validToken(USER1));
    });

    test('Try publishing a listing review with no contents', async () => {
      const listingid = await singleListingId();
      const bookingid = await singleBookingId();
      await putTry(`/listings/${listingid}/review/${bookingid}`, 400, {}, await validToken(USER1));
    });

    test('Try publishing a listing review with a fake listingid', async () => {
      const listingid = '123456';
      const bookingid = await singleBookingId();
      const review = { text: 'Great Place!', rating: 5 };
      await putTry(`/listings/${listingid}/review/${bookingid}`, 400, review, await validToken(USER1));
    });

    test('Try publishing a listing review for a listing the user has not stayed at', async () => {
      // Creating a listing under USER2
      const body1 = await postTry(
        '/listings/new',
        200,
        {
          title: LISTING1.title,
          address: LISTING1.address,
          price: LISTING1.price,
          thumbnail: LISTING1.thumbnail,
          metadata: LISTING1.metadata,
        },
        await validToken(USER2),
      );
      const listingid = body1.listingId;

      const bookingid = await singleBookingId();
      const review = { text: 'Great Place!', rating: 5 };
      await putTry(`/listings/${listingid}/review/${bookingid}`, 400, review, await validToken(USER1));

      // Clean up
      await deleteTry(`/listings/${listingid}`, 200, {}, await validToken(USER2));
    });
  });

  describe('Publishing a single listing review', () => {
    test('Publishing a single review', async () => {
      const listingid = await singleListingId();
      const bookingid = await singleBookingId();

      const review = { text: 'Great Place!', rating: 5 };
      await putTry(`/listings/${listingid}/review/${bookingid}`, 200, { review }, await validToken(USER2));
    });

    test('Checking there is now a single review for this listing', async () => {
      const listingid = await singleListingId();
      const { listing } = await getTry(`/listings/${listingid}`, 200, {});

      expect(listing.reviews).toMatchObject([{ text: 'Great Place!', rating: 5 }]);
    });
  });

  describe('Publishing a secondary listing review', () => {
    test('Publishing a secondary review', async () => {
      const listingid = await singleListingId();
      const bookingid = await singleBookingId();

      const review = { text: 'Just ok, like my life', rating: 3 };
      await putTry(`/listings/${listingid}/review/${bookingid}`, 200, { review }, await validToken(USER2));
    });

    test('Checking there is now a single review for this listing', async () => {
      const listingid = await singleListingId();
      const { listing } = await getTry(`/listings/${listingid}`, 200, {});

      expect(listing.reviews).toMatchObject([
        { text: 'Great Place!', rating: 5 },
        { text: 'Just ok, like my life', rating: 3 },
      ]);
    });
  });
});
